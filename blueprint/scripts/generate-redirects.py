#!/usr/bin/env python3
"""Generate stable theorem routes from Verso Blueprint's preview manifest."""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
import sys
from html.parser import HTMLParser
from pathlib import Path, PurePosixPath
from urllib.parse import urlsplit

sys.path.insert(0, str(Path(__file__).resolve().parent))
import paper_sources  # noqa: E402


SLUG = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
COMMIT = re.compile(r"^[0-9a-f]{40}$")


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


def locate_paper_sources(
    entries: list[dict], main_tex: Path
) -> tuple[list[str], dict[str, tuple[int, int]]]:
    """Find every entry in main.tex by label; warn about unlinked numbered results."""
    lines = main_tex.read_text(encoding="utf-8").splitlines()
    spans = paper_sources.paper_spans(lines, entries)
    for kind, line_number in paper_sources.unlinked_environments(lines, entries):
        print(
            f"warning: main.tex:{line_number}: \\begin{{{kind}}} has no blueprint entry",
            file=sys.stderr,
        )
    return lines, spans


def validate_pdf_link_badges(
    entries: list[dict], lines: list[str], spans: dict[str, tuple[int, int]]
) -> None:
    """Require one correctly placed LaTeX badge for every PDF-linked result."""
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
        start_line, end_line = spans[entry["label"]]
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
    if any("source" in entry for entry in entries):
        raise ValueError(
            "links.json entries must not pin line numbers; paper locations are derived "
            "from \\label{...} and % blueprint-begin/end markers in main.tex"
        )
    paper_lines, spans = locate_paper_sources(entries, args.links.parent.parent / "main.tex")
    validate_pdf_link_badges(entries, paper_lines, spans)

    previews = load_previews(args.manifest)
    targets = statement_targets(previews)
    declarations = lean_declaration_index(previews)
    repository = links.get("repository")
    if not isinstance(repository, str) or not repository.startswith("https://github.com/"):
        raise ValueError("links manifest must declare its canonical GitHub repository")
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
        start_line, end_line = spans[label]
        expected_source = {"path": "main.tex", "startLine": start_line, "endLine": end_line}
        actual_source = source_span(preview)
        if (
            actual_source.get("startLine") != start_line
            or actual_source.get("endLine") != end_line
            or not str(actual_source.get("path", "")).endswith("main.tex")
        ):
            raise ValueError(
                f"paper source drift for {label!r}: main.tex has {expected_source}, Verso "
                f"rendered {actual_source}; regenerate PaperSources.lean with "
                "scripts/paper_sources.py and rebuild"
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
                "source": expected_source,
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
