#!/usr/bin/env python3
"""Generate stable theorem routes from Verso Blueprint's preview manifest."""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
from html.parser import HTMLParser
from pathlib import Path, PurePosixPath
from urllib.parse import urlsplit


SLUG = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
COMMIT = re.compile(r"^[0-9a-f]{40}$")
CORRESPONDENCE_TAGS = {"direct", "corrected", "factored", "encoding"}


class IdCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.ids: set[str] = set()

    def handle_starttag(self, _tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for name, value in attrs:
            if name == "id" and value is not None:
                self.ids.add(value)


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--links", type=Path, required=True)
    parser.add_argument("--semantic-review", type=Path, required=True)
    parser.add_argument("--site", type=Path, required=True)
    parser.add_argument("--expected-commit", required=True)
    return parser.parse_args()


def safe_href(href: str) -> str:
    split = urlsplit(href)
    if split.scheme or split.netloc or href.startswith("/"):
        raise ValueError(f"preview href must be site-relative, got {href!r}")
    path = PurePosixPath(split.path)
    if ".." in path.parts:
        raise ValueError(f"preview href may not escape the site, got {href!r}")
    return href


def validate_target(site: Path, href: str) -> None:
    split = urlsplit(safe_href(href))
    target = site.joinpath(*PurePosixPath(split.path).parts)
    if split.path.endswith("/"):
        target /= "index.html"
    if not target.is_file():
        raise ValueError(f"preview target does not exist: {href!r} ({target})")
    if split.fragment:
        parser = IdCollector()
        parser.feed(target.read_text(encoding="utf-8"))
        if split.fragment not in parser.ids:
            raise ValueError(f"preview fragment does not exist: {href!r}")


def load_previews(path: Path) -> list[dict]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    previews = raw.get("previews")
    if not isinstance(previews, list):
        raise ValueError(f"{path} does not contain a previews array")
    return previews


def statement_targets(previews: list[dict]) -> dict[str, dict]:
    matches: dict[str, list[dict]] = {}
    for preview in previews:
        if preview.get("facet") != "statement" or preview.get("targetKind") != "block":
            continue
        label = preview.get("authoredLabel")
        if isinstance(label, str):
            matches.setdefault(label, []).append(preview)

    result: dict[str, dict] = {}
    for label, entries in matches.items():
        if len(entries) != 1:
            raise ValueError(f"label {label!r} has {len(entries)} block statement targets")
        href = entries[0].get("href")
        if not isinstance(href, str):
            raise ValueError(f"label {label!r} has no href")
        safe_href(href)
        result[label] = entries[0]
    return result


def lean_declaration_index(previews: list[dict]) -> dict[str, dict]:
    result: dict[str, dict] = {}
    for preview in previews:
        if preview.get("facet") != "statement" or preview.get("targetKind") != "leanDecl":
            continue
        key = preview.get("key")
        if not isinstance(key, str):
            continue
        if key in result:
            raise ValueError(f"duplicate Lean declaration preview key: {key}")
        result[key] = preview
    return result


def source_span(preview: dict) -> dict:
    matches = []
    for source in preview.get("sources", []):
        if source.get("document") == "paper-source":
            matches.extend(source.get("spans", []))
    if len(matches) != 1 or not isinstance(matches[0].get("text"), dict):
        raise ValueError(
            f"{preview.get('authoredLabel')!r} must have exactly one paper-source text span"
        )
    return matches[0]["text"]


def semantic_review_records(path: Path) -> dict[str, dict]:
    text = path.read_text(encoding="utf-8")
    sections = re.split(r"(?m)^### [0-9]+[.] ", text)[1:]
    result: dict[str, dict] = {}
    for section in sections:
        label_match = re.search(r"[*][*]Canonical ID:[*][*] `([^`]+)`", section)
        category_match = re.search(r"[*][*]Category:[*][*] ([^\n]+)", section)
        route_match = re.search(r"[*][*]Stable route:[*][*] `([^`]+)`", section)
        source_match = re.search(
            r"[*][*]LaTeX source:[*][*] `([^`:]+):([0-9]+)-([0-9]+)`", section
        )
        if any(match is None for match in (label_match, category_match, route_match, source_match)):
            continue
        label = label_match.group(1)
        categories = {item.strip() for item in category_match.group(1).split(",")}
        if label in result:
            raise ValueError(f"duplicate semantic-review record for {label!r}")
        result[label] = {
            "categories": categories,
            "route": route_match.group(1),
            "source": {
                "path": source_match.group(1),
                "startLine": int(source_match.group(2)),
                "endLine": int(source_match.group(3)),
            },
        }
    if not result:
        raise ValueError(f"{path} contains no semantic-review records")
    return result


def validate_numbered_paper_environments(entries: list[dict], links_path: Path) -> None:
    repository_root = links_path.parent.parent
    numbered = [entry for entry in entries if entry.get("numbered") is True]
    source_paths = {entry.get("source", {}).get("path") for entry in numbered}
    if source_paths != {"main.tex"}:
        raise ValueError(
            "numbered entries must all point to main.tex, got "
            f"{sorted(map(repr, source_paths))}"
        )
    source_path = repository_root / "main.tex"
    lines = source_path.read_text(encoding="utf-8").splitlines()
    environment_pattern = re.compile(r"^\\begin[{](theorem|definition|proposition|lemma)[}]")
    actual = {
        (match.group(1), line_number)
        for line_number, line in enumerate(lines, start=1)
        if (match := environment_pattern.match(line)) is not None
    }
    expected = {
        (entry.get("kind"), entry.get("source", {}).get("startLine")) for entry in numbered
    }
    if actual != expected:
        raise ValueError(
            "numbered paper-environment coverage drift: "
            f"missing {sorted(actual - expected)}, stale {sorted(expected - actual)}"
        )
    for entry in numbered:
        source = entry["source"]
        end_line = source.get("endLine")
        kind = entry.get("kind")
        if not isinstance(end_line, int) or not 1 <= end_line <= len(lines):
            raise ValueError(f"invalid paper end line for {entry.get('label')!r}: {end_line!r}")
        if lines[end_line - 1].strip() != rf"\end{{{kind}}}":
            raise ValueError(
                f"paper source range for {entry.get('label')!r} does not end at "
                f"\\end{{{kind}}}"
            )


def validate_pdf_link_badges(entries: list[dict], links_path: Path) -> None:
    """Require one correctly placed LaTeX badge for every reviewed PDF result."""
    repository_root = links_path.parent.parent
    source_path = repository_root / "main.tex"
    lines = source_path.read_text(encoding="utf-8").splitlines()
    badge_pattern = re.compile(r"^\\leanblueprint[{]([a-z0-9]+(?:-[a-z0-9]+)*)[}]$")
    actual: dict[str, list[int]] = {}
    for line_number, line in enumerate(lines, start=1):
        if match := badge_pattern.fullmatch(line.strip()):
            actual.setdefault(match.group(1), []).append(line_number)

    linked = [
        entry
        for entry in entries
        if entry.get("numbered") is True or entry.get("pdfLinked") is True
    ]
    expected = {entry.get("slug") for entry in linked}
    if set(actual) != expected:
        raise ValueError(
            "PDF badge coverage drift: "
            f"missing {sorted(expected - set(actual))}, "
            f"stale {sorted(set(actual) - expected)}"
        )
    for entry in linked:
        slug = entry["slug"]
        badge_lines = actual[slug]
        if len(badge_lines) != 1:
            raise ValueError(f"PDF badge {slug!r} occurs {len(badge_lines)} times")
        source = entry.get("source", {})
        start_line = source.get("startLine")
        end_line = source.get("endLine")
        if not isinstance(start_line, int) or not isinstance(end_line, int):
            raise ValueError(f"invalid source span for PDF badge {slug!r}")
        if not start_line <= badge_lines[0] <= end_line:
            raise ValueError(
                f"PDF badge {slug!r} is on line {badge_lines[0]}, outside "
                f"its source span {start_line}-{end_line}"
            )


def validated_declarations(
    preview: dict, declaration_previews: dict[str, dict], repository: str
) -> tuple[list[dict], set[str]]:
    keys = preview.get("leanCodePreviewKeys")
    if not isinstance(keys, list) or not keys:
        raise ValueError(f"{preview.get('authoredLabel')!r} has no associated Lean declarations")
    source_pattern = re.compile(
        rf"^{re.escape(repository)}/blob/([0-9a-f]{{40}})/.+[.]lean#L[1-9][0-9]*(?:-L[1-9][0-9]*)?$"
    )
    declarations: list[dict] = []
    commits: set[str] = set()
    for key in keys:
        try:
            declaration = declaration_previews[key]
        except KeyError as error:
            raise ValueError(f"missing Lean declaration preview {key!r}") from error
        location_result = declaration.get("sourceLocation")
        if not isinstance(location_result, dict) or location_result.get("ok") is not True:
            raise ValueError(
                f"Lean source unavailable for {declaration.get('authoredLabel')!r}: "
                f"{location_result}"
            )
        location = location_result.get("location")
        href = location.get("href") if isinstance(location, dict) else None
        if not isinstance(href, str) or (match := source_pattern.fullmatch(href)) is None:
            raise ValueError(
                f"Lean source for {declaration.get('authoredLabel')!r} is not a "
                f"commit-pinned GitHub line link: {href!r}"
            )
        commits.add(match.group(1))
        declarations.append(
            {"name": declaration.get("authoredLabel", declaration.get("label")), "sourceHref": href}
        )
    return declarations, commits


def redirect_page(*, title: str, target: str) -> str:
    escaped_title = html.escape(title)
    escaped_target = html.escape(target, quote=True)
    js_target = json.dumps(target)
    return f"""<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <meta http-equiv="refresh" content="0; url={escaped_target}">
    <link rel="canonical" href="{escaped_target}">
    <title>{escaped_title} — Lean formalisation</title>
    <script>window.location.replace({js_target});</script>
  </head>
  <body>
    <p>Continue to <a href="{escaped_target}">{escaped_title}</a>.</p>
  </body>
</html>
"""


def main() -> None:
    args = arguments()
    if not COMMIT.fullmatch(args.expected_commit):
        raise ValueError(f"expected commit must be a full lowercase Git SHA: {args.expected_commit!r}")
    links = json.loads(args.links.read_text(encoding="utf-8"))
    entries = links.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError(f"{args.links} does not contain a nonempty entries array")
    validate_numbered_paper_environments(entries, args.links)
    validate_pdf_link_badges(entries, args.links)
    review_records = semantic_review_records(args.semantic_review)
    reviewed_labels = {
        entry.get("label")
        for entry in entries
        if entry.get("numbered") is True or entry.get("pdfLinked") is True
    }
    if set(review_records) != reviewed_labels:
        raise ValueError(
            "semantic-review coverage drift: "
            f"missing {sorted(reviewed_labels - set(review_records))}, "
            f"stale {sorted(set(review_records) - reviewed_labels)}"
        )

    previews = load_previews(args.manifest)
    targets = statement_targets(previews)
    declarations = lean_declaration_index(previews)
    repository = links.get("repository")
    if not isinstance(repository, str) or not repository.startswith("https://github.com/"):
        raise ValueError("links manifest must declare its canonical GitHub repository")
    review_state = links.get("reviewState")
    if not isinstance(review_state, str) or not review_state:
        raise ValueError("links manifest must declare a nonempty review state")
    seen_slugs: set[str] = set()
    seen_labels: set[str] = set()
    resolved: list[dict] = []
    route_root = args.site / "theorems"
    if route_root.exists():
        shutil.rmtree(route_root)

    for entry in entries:
        slug = entry.get("slug")
        label = entry.get("label")
        if not isinstance(slug, str) or not SLUG.fullmatch(slug):
            raise ValueError(f"invalid theorem slug: {slug!r}")
        if not isinstance(label, str) or not label:
            raise ValueError(f"invalid blueprint label for {slug!r}: {label!r}")
        if slug in seen_slugs:
            raise ValueError(f"duplicate theorem slug: {slug}")
        if label in seen_labels:
            raise ValueError(f"duplicate blueprint label: {label}")
        seen_slugs.add(slug)
        seen_labels.add(label)

        try:
            preview = targets[label]
        except KeyError as error:
            raise ValueError(f"no block statement preview found for {label!r}") from error
        href = preview["href"]
        validate_target(args.site, href)

        paper_ref = entry.get("paperRef")
        if entry.get("numbered") is True and preview.get("title") != paper_ref:
            raise ValueError(
                f"paper numbering drift for {label!r}: expected {paper_ref!r}, "
                f"Verso rendered {preview.get('title')!r}"
            )
        tags = set(preview.get("tags", []))
        expected_correspondence = set(entry.get("correspondence", []))
        if not expected_correspondence or not expected_correspondence <= CORRESPONDENCE_TAGS:
            raise ValueError(
                f"{label!r} has invalid correspondence categories: "
                f"{sorted(expected_correspondence)}"
            )
        if entry.get("numbered") is True or entry.get("pdfLinked") is True:
            review_record = review_records[label]
            if review_record["categories"] != expected_correspondence:
                raise ValueError(
                    f"semantic-review category drift for {label!r}: ledger has "
                    f"{sorted(review_record['categories'])}, links manifest has "
                    f"{sorted(expected_correspondence)}"
                )
            if review_record["source"] != entry.get("source"):
                raise ValueError(
                    f"semantic-review source drift for {label!r}: ledger has "
                    f"{review_record['source']}, links manifest has {entry.get('source')}"
                )
            expected_route = f"/theorems/{slug}/"
            if review_record["route"] != expected_route:
                raise ValueError(
                    f"semantic-review route drift for {label!r}: ledger has "
                    f"{review_record['route']!r}, expected {expected_route!r}"
                )
        actual_correspondence = tags & CORRESPONDENCE_TAGS
        if actual_correspondence != expected_correspondence:
            raise ValueError(
                f"correspondence drift for {label!r}: expected "
                f"{sorted(expected_correspondence)}, got {sorted(actual_correspondence)}"
            )
        required_tags = {review_state, *expected_correspondence}
        if not required_tags <= tags:
            raise ValueError(f"{label!r} is missing tags {sorted(required_tags - tags)}")
        expected_source = entry.get("source", {})
        actual_source = source_span(preview)
        if (
            actual_source.get("startLine") != expected_source.get("startLine")
            or actual_source.get("endLine") != expected_source.get("endLine")
            or not str(actual_source.get("path", "")).endswith(expected_source.get("path", ""))
        ):
            raise ValueError(
                f"paper source drift for {label!r}: expected {expected_source}, got {actual_source}"
            )
        lean_declarations, source_commits = validated_declarations(
            preview, declarations, repository
        )
        if source_commits != {args.expected_commit}:
            raise ValueError(
                f"{label!r} source links must target {args.expected_commit}, got "
                f"{sorted(source_commits)}"
            )

        route_dir = route_root / slug
        route_dir.mkdir(parents=True, exist_ok=False)
        target = "../../" + href
        route_dir.joinpath("index.html").write_text(
            redirect_page(title=paper_ref or label, target=target),
            encoding="utf-8",
        )
        resolved.append(
            {
                **entry,
                "route": f"/theorems/{slug}/",
                "targetHref": href,
                "sourceCommit": next(iter(source_commits)),
                "leanDeclarations": lean_declarations,
            }
        )

    output = {**links, "entries": resolved}
    args.site.joinpath("links.json").write_text(
        json.dumps(output, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    numbered = sum(entry.get("numbered") is True for entry in resolved)
    print(
        f"validated {len(resolved)} paper nodes ({numbered} numbered), "
        f"{sum(len(entry['leanDeclarations']) for entry in resolved)} Lean source links"
    )
    print(f"generated {len(resolved)} stable theorem routes in {route_root}")


if __name__ == "__main__":
    main()
