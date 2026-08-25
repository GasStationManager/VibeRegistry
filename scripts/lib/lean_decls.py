#!/usr/bin/env python3
"""Locate declarations inside a Lean source file, by fully-qualified name.

Used to lift the exact statement text of a registered declaration out of its
spec file — for sign-off packets and for the statement search index — without a
Lean toolchain. This is a source scanner, not a parser: it tracks `namespace`
/`end` nesting and `open`-free declaration headers, which is all the spec-file
conventions require (see CLAUDE.md: specs are plain statements, no tactic
blocks beyond `:= by sorry`).

API:
    find_declarations(text) -> list[Declaration]
    find_declaration(text, "QLS.Stoch.robbinsSiegmund_expBound") -> Declaration | None
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

# Declaration keywords whose statements we may want to show a reviewer.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "inductive",
    "instance",
    "opaque",
    "axiom",
    "class",
)

# Modifiers that may sit in front of the keyword.
MODIFIERS = (
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
    "@[simp]",
)

_DECL_RE = re.compile(
    r"^(?P<indent>\s*)"
    r"(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*)"
    r"(?P<kw>" + "|".join(DECL_KEYWORDS) + r")\s+"
    r"(?P<name>[^\s:({\[⦃{]+)"
)

_NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>\S+)")
_SECTION_RE = re.compile(r"^\s*section\b(?:\s+(?P<name>\S+))?")
_END_RE = re.compile(r"^\s*end\b(?:\s+(?P<name>\S+))?")


@dataclass
class Declaration:
    name: str            # fully qualified, e.g. QLS.Stoch.robbinsSiegmund_expBound
    short_name: str      # as written in the source
    kind: str            # theorem / def / ...
    start_line: int      # 1-indexed, first line of the declaration header
    end_line: int        # 1-indexed, last line of the declaration
    doc: str = ""        # preceding /-- ... -/ docstring, if any
    source: str = ""     # the declaration text itself
    namespaces: list = field(default_factory=list)

    def to_dict(self):
        return {
            "name": self.name,
            "kind": self.kind,
            "start_line": self.start_line,
            "end_line": self.end_line,
            "doc": self.doc,
            "source": self.source,
        }


def _strip_universe_suffix(name: str) -> str:
    """`foo.{v}` declares `foo` (the regex stops at `{`, leaving a trailing dot)."""
    return name.split(".{", 1)[0].rstrip(".")


def _collect_doc(lines, decl_line_idx):
    """Return the `/-- ... -/` docstring immediately above a declaration."""
    i = decl_line_idx - 1
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i < 0 or not lines[i].rstrip().endswith("-/"):
        return ""
    end = i
    while i >= 0 and "/--" not in lines[i]:
        i -= 1
    if i < 0:
        return ""
    doc = "\n".join(lines[i:end + 1])
    doc = doc.replace("/--", "", 1)
    doc = doc[::-1].replace("/-", "", 1)[::-1]
    return doc.strip()


def find_declarations(text: str):
    """Scan Lean source and return every top-level-ish declaration it contains."""
    lines = text.split("\n")
    stack = []       # open `namespace`/`section` names, innermost last
    decls = []
    in_block_comment = False
    pending = None   # declaration whose extent we are still consuming

    def close(end_idx):
        nonlocal pending
        if pending is None:
            return
        decl, start_idx = pending
        end = end_idx
        while end > start_idx and not lines[end - 1].strip():
            end -= 1
        # A doc comment sitting just above the next declaration belongs to that
        # declaration, not to this one — do not swallow it.
        if end > start_idx and lines[end - 1].rstrip().endswith("-/"):
            probe = end - 1
            while probe > start_idx and "/-" not in lines[probe]:
                probe -= 1
            if probe > start_idx and "/-" in lines[probe]:
                end = probe
                while end > start_idx and not lines[end - 1].strip():
                    end -= 1
        decl.end_line = end
        decl.source = "\n".join(lines[start_idx:end]).rstrip()
        decls.append(decl)
        pending = None

    for idx, line in enumerate(lines):
        stripped = line.strip()

        # Track block comments so `namespace`/`theorem` inside them is ignored.
        if in_block_comment:
            if "-/" in stripped:
                in_block_comment = False
            continue
        if stripped.startswith("/-") and "-/" not in stripped:
            in_block_comment = True
            continue
        if stripped.startswith("--"):
            continue

        ns = _NAMESPACE_RE.match(line)
        if ns:
            close(idx)
            stack.extend(ns.group("name").split("."))
            continue

        sec = _SECTION_RE.match(line)
        if sec:
            close(idx)
            stack.append(None)  # sections do not contribute to names
            continue

        end_m = _END_RE.match(line)
        if end_m:
            close(idx)
            name = end_m.group("name")
            if name:
                for _ in name.split("."):
                    if stack:
                        stack.pop()
            elif stack:
                stack.pop()
            continue

        decl = _DECL_RE.match(line)
        if decl:
            close(idx)
            short = _strip_universe_suffix(decl.group("name"))
            prefix = [n for n in stack if n]
            # A declaration may carry its own dotted prefix (`Foo.bar`).
            full = ".".join(prefix + [short]) if prefix else short
            pending = (
                Declaration(
                    name=full,
                    short_name=short,
                    kind=decl.group("kw"),
                    start_line=idx + 1,
                    end_line=idx + 1,
                    doc=_collect_doc(lines, idx),
                    namespaces=list(prefix),
                ),
                idx,
            )

    close(len(lines))
    return decls


def find_declaration(text: str, name: str):
    """Find one declaration by fully-qualified name (or by short name as a fallback)."""
    decls = find_declarations(text)
    for decl in decls:
        if decl.name == name:
            return decl
    # Fallback: the entry may name a declaration whose namespace the spec opens
    # rather than nests (both are legal and both occur in practice).
    tail = name.split(".")[-1]
    matches = [d for d in decls if d.short_name == tail or d.name.endswith("." + tail)]
    if len(matches) == 1:
        return matches[0]
    return None
