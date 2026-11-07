#!/usr/bin/env python3
"""Build source indexes and check the paper-to-Lean and exact-check mapping.

Run from any directory with Python 3.11 or later:

    python3 -S -s -B paper-lean-mapping/build_and_check.py

The output is identical under -O. Only the standard library is used. The
script reads the TeX sources, the Lean sources, the exact checkers, the list
of their check families, the file inventory of the numerical illustrations
(whose paths the mapping gives relative to verification/numerics/) and the
mapping; it writes nothing. It does not compile Lean, build the PDF,
run the exact checks or run the numerical illustrations.
"""

import ast
import copy
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
MAPPING = "paper-lean-mapping/mapping.json"
BY_SECTION = "paper-lean-mapping/by-section.md"
PAPER = "paper/main.tex"
LEAN_ROOT = "lean"
LIBRARY = "KE02"
AXIOM_PROBE = "lean/audit/Axioms.lean"
EXACT_FOLDER = "verification/core"
CHECKERS_TXT = "verification/core/CHECKERS.txt"
EXACT_CHECKERS = ("check_constants.py", "check_appendix_a.py")
NUMERICS = "verification/numerics"
NUMERICS_INVENTORY = "<numerics inventory>"
# The theorem-like environments of the paper: each has its own counter, reset
# at every numbered section except where marked global.
THEOREM_DECLARATIONS = (
    r"\newtheorem{proposition}{Proposition}[section]",
    r"\newtheorem{theorem}{Theorem}[section]",
    r"\newtheorem{corollary}{Corollary}[section]",
    r"\newtheorem{lemma}{Lemma}[section]",
    r"\newtheorem{example}{Example}[section]",
    r"\newtheorem{remark}{Remark}[section]",
    r"\newtheorem{assumption}{Assumption}",
    r"\newtheorem{definition}{Definition}[section]",
)
ENVIRONMENTS = {
    "proposition": "Proposition", "theorem": "Theorem", "corollary": "Corollary",
    "lemma": "Lemma", "example": "Example", "remark": "Remark", "assumption": "Assumption",
    "definition": "Definition", "algorithm": "Algorithm",
}
GLOBAL_COUNTERS = frozenset({"assumption", "algorithm"})
FLOATS = {"figure": "Figure", "table": "Table"}
COVERAGES = {
    "formalized_in_full": "Formalized in full",
    "formalized_scalar_part": "Formalized scalar part only",
    "exact_cross_check_only": "Exact finite cross-check only",
    "written_proof_only": "Written proof only",
}
RESULT_HEADER = "| Result | Label | Page | Title | Coverage |"
STEP_HEADER = "| Anchor | Label | Page | Title |"
TABLE_RULE_5 = "| --- | --- | --- | --- | --- |"
TABLE_RULE_4 = "| --- | --- | --- | --- |"
IDENT = r"[^\W\d][\w']*"
QUALIFIED = r"[^\W\d][\w'.]*"
DECLARATION = re.compile(
    r"(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(def|theorem|lemma|structure|abbrev|instance|inductive|class)\s+(" + IDENT + r")(.*)")
PROOF_KINDS = frozenset({"theorem", "lemma"})


def need(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def matched(match, message):
    """Return a regular-expression match, or fail closed if there is none."""
    if match is None:
        raise SystemExit("FAIL: " + message)
    return match


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def reject_number(value):
    raise SystemExit("FAIL: unsupported JSON number")


def parse_json(data):
    return json.loads(data, object_pairs_hook=unique_object,
                      parse_float=reject_number, parse_constant=reject_number)


def keys(value, expected, label):
    need(isinstance(value, dict) and set(value) == set(expected), label + " fields")


def string(value, label):
    need(isinstance(value, str) and value.strip() != "", label + " text")


def strings(values, label):
    need(isinstance(values, list) and all(isinstance(x, str) for x in values), label)
    need(len(values) == len(set(values)), "duplicate " + label)
    for value in values:
        string(value, label)


def positive_int(value, label):
    need(type(value) is int and value > 0, label)


def safe_path(name):
    need(isinstance(name, str) and name != "" and "\\" not in name, "source path")
    p = Path(name)
    need(not p.is_absolute() and ".." not in p.parts and p.as_posix() == name, "source path")
    return p


def relative(path):
    return path.relative_to(ROOT).as_posix()


def regular(path, name):
    need(path.is_file() and not path.is_symlink() and path.resolve() == path,
         "missing or linked source: " + name)


def read_inputs():
    names = {MAPPING, BY_SECTION, CHECKERS_TXT, AXIOM_PROBE, LEAN_ROOT + "/" + LIBRARY + ".lean"}
    names.update(relative(p) for p in (ROOT / "paper").rglob("*.tex")
                 if not relative(p).startswith("paper/build/"))
    names.update(relative(p) for p in (ROOT / LEAN_ROOT / LIBRARY).rglob("*.lean"))
    names.update(relative(p) for p in (ROOT / EXACT_FOLDER).glob("*.py"))
    result = {}
    for name in sorted(names):
        p = ROOT / safe_path(name)
        regular(p, name)
        need(p.stat().st_size <= 4000000, "oversized source: " + name)
        result[name] = p.read_text(encoding="utf-8")
    inventory = []
    for p in sorted((ROOT / NUMERICS).rglob("*")):
        name = p.relative_to(ROOT / NUMERICS).as_posix()
        need(not p.is_symlink(), "linked numerics file: " + name)
        if p.is_file():
            need("__pycache__" not in p.parts, "bytecode cache: " + name)
            inventory.append(name)
    need(bool(inventory), "empty numerics folder")
    result[NUMERICS_INVENTORY] = "\n".join(inventory)
    return result


# ------------------------------------------------------------------ TeX index

def tex_uncomment(line):
    for i, char in enumerate(line):
        if char == "%":
            j = i - 1
            while j >= 0 and line[j] == "\\":
                j -= 1
            if (i - j - 1) % 2 == 0:
                return line[:i]
    return line


def balanced(text, start, opening, closing):
    """Return the end offset of the group opened at text[start] == opening."""
    need(text[start] == opening, "unbalanced TeX group")
    depth = 0
    for i in range(start, len(text)):
        char = text[i]
        if char == "\\":
            continue
        if char == "{" and opening != "{":
            depth += 100
        elif char == "}" and opening != "{":
            depth -= 100
        elif char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0:
                return i + 1
    raise SystemExit("FAIL: unbalanced TeX group")


def appendix_letter(count):
    need(1 <= count <= 26, "unsupported appendix count")
    return chr(ord("A") + count - 1)


def paper_index(sources, entry):
    """Index sections, theorem-like results, algorithms, equations, floats and labels."""
    seen = set()

    def expand(name):
        safe_path(name)
        need(name.startswith("paper/") and name.endswith(".tex"), "paper input path")
        need(name in sources, "missing paper input: " + name)
        need(name not in seen, "repeated paper input: " + name)
        seen.add(name)
        output = []
        for line in sources[name].splitlines():
            line = tex_uncomment(line)
            if re.search(r"\\(?:input|include)\b", line):
                match = matched(re.fullmatch(r"\s*\\input\{([A-Za-z0-9_/-]+?)(?:\.tex)?\}\s*", line),
                                "unsupported paper inclusion")
                output.extend(expand("paper/" + match.group(1) + ".tex"))
            else:
                output.append((name, line))
        return output

    expanded = expand(entry)
    need(seen == {n for n in sources if n.startswith("paper/") and n.endswith(".tex")},
         "unreferenced paper source")
    text = "\n".join(line for _, line in expanded)
    declarations = tuple(re.findall(r"\\newtheorem(?:\*)?[^\n]*", text))
    need(declarations == THEOREM_DECLARATIONS, "unsupported theorem counter declaration")
    need(not re.search(r"\\(?:setcounter|addtocounter|counterwithin|counterwithout|numberwithin|"
                       r"tag|nonumber|notag|stepcounter|refstepcounter)\b", text),
         "unsupported paper counter modification")
    need(not re.search(r"\\begin\{(?:align|gather|multline|eqnarray|flalign|alignat)\*?\}", text),
         "unsupported numbered display environment")
    packages = re.findall(r"\\usepackage(\[[^\]]*\])?\{algorithm2e\}", text)
    need(len(packages) == 1 and set(packages[0].strip("[]").split(",")) <= {"ruled", "vlined", ""},
         "unsupported algorithm numbering")
    need(text.count(r"\appendix") <= 1, "unsupported appendix markup")
    token = re.compile(
        r"\\(section|subsection)(\*)?\{([^{}]+)\}|\\(appendix)\b|"
        r"\\(begin|end)\{([^{}]+)\}|\\label\{([^{}]+)\}|\\caption\{")
    sections, results, labels, stack = [], [], {}, []
    section, subsection, appendix = "", "", False
    section_count = appendix_count = 0
    counters = {env: 0 for env in ENVIRONMENTS}
    counters.update({"equation": 0, "figure": 0, "table": 0})
    context = None
    active = None
    for source, line in expanded:
        for match in token.finditer(line):
            level, starred, title, appendix_cmd, command, env, label = match.groups()[:7]
            if appendix_cmd:
                need(active is None and not stack[1:], "appendix inside an environment")
                appendix = True
            elif level is not None:
                need(active is None, "section inside numbered result")
                if starred:
                    continue
                if level == "section":
                    if appendix:
                        appendix_count += 1
                        section = appendix_letter(appendix_count)
                    else:
                        section_count += 1
                        section = str(section_count)
                    subsection = ""
                    for env_name in ENVIRONMENTS:
                        if env_name not in GLOBAL_COUNTERS:
                            counters[env_name] = 0
                    sections.append({"number": section, "title": title, "source": source})
                    context = ("section", section)
                else:
                    need(section != "", "unsectioned subsection")
                    subsection = section + "." + str(int(subsection.rpartition(".")[2] or 0) + 1)
                    context = ("subsection", subsection)
            elif command == "begin":
                stack.append({"env": env, "context": None})
                if env in ENVIRONMENTS:
                    need(active is None and section != "", "nested or unsectioned numbered result")
                    counters[env] += 1
                    number = (str(counters[env]) if env in GLOBAL_COUNTERS
                              else section + "." + str(counters[env]))
                    rest = line[match.end():]
                    title = None
                    if env != "algorithm" and rest.startswith("["):
                        end = balanced(rest, 0, "[", "]")
                        title = rest[1:end - 1].strip()
                    active = {"environment": env, "number": number, "section": section,
                              "source": source, "labels": [], "depth": len(stack),
                              "title": title}
                    stack[-1]["context"] = (env, number)
                elif env == "equation":
                    counters["equation"] += 1
                    stack[-1]["context"] = ("equation", str(counters["equation"]))
                elif env in FLOATS:
                    counters[env] += 1
                    stack[-1]["context"] = (env, str(counters[env]))
                need(env.rstrip("*") not in ENVIRONMENTS or env in ENVIRONMENTS,
                     "unsupported unnumbered result environment")
            elif command == "end":
                need(stack and stack[-1]["env"] == env, "unbalanced paper environment")
                if active is not None and len(stack) == active["depth"]:
                    need(bool(active["labels"]), "numbered result requires a direct label")
                    need(active["title"] is not None, "numbered result requires a title")
                    results.append({k: active[k] for k in
                                    ("environment", "number", "section", "source", "labels",
                                     "title")})
                    active = None
                stack.pop()
            elif label is not None:
                need(label not in labels, "duplicate paper label")
                inner = [item["context"] for item in stack if item["context"] is not None]
                kind, number = inner[-1] if inner else (context or ("none", ""))
                labels[label] = {"section": section, "source": source, "kind": kind,
                                 "number": number}
                if active is not None and len(stack) == active["depth"]:
                    active["labels"].append(label)
            else:
                if active is not None and active["environment"] == "algorithm" and \
                        len(stack) == active["depth"]:
                    rest = line[match.end() - 1:]
                    end = balanced(rest, 0, "{", "}")
                    need(active["title"] is None, "repeated algorithm caption")
                    active["title"] = rest[1:end - 1].strip()
    need(not stack and active is None, "unclosed paper environment")
    names = {label: ENVIRONMENTS[r["environment"]] + " " + r["number"]
             for r in results for label in r["labels"]}
    for record in results:
        title = record["title"]
        for match in re.finditer(r"\\[Cc]ref\{([^{}]+)\}", title):
            need(match.group(1) in names, "title reference")
        title = re.sub(r"\\[Cc]ref\{([^{}]+)\}", lambda m: names[m.group(1)], title)
        need(not re.search(r"[\\{}$`|]", title), "unsupported result title markup")
        record["title"] = title
    return sections, results, labels


# ------------------------------------------------------------------ Lean index

def lean_without_comments(text):
    """Mask strings and nested comments, keeping line structure."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            if text[i] == "\\":
                need(i + 1 < len(text), "unterminated Lean string")
                out.append("  ")
                i += 2
            else:
                quoted = text[i] != '"'
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        elif text[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    need(not depth and not quoted, "unterminated Lean comment or string")
    return "".join(out)


def lean_index(sources):
    """Index top-level declarations, structure fields, `where` assignments and
    anonymous-constructor bodies of the library sources."""
    declarations = {}
    for source in sorted(sources):
        if not (source == LEAN_ROOT + "/" + LIBRARY + ".lean" or
                (source.startswith(LEAN_ROOT + "/" + LIBRARY + "/") and source.endswith(".lean"))):
            continue
        scopes = []
        current = None
        member = None
        for line in lean_without_comments(sources[source]).splitlines():
            if not line.strip():
                continue
            if line[0] not in " \t":
                current = member = None
                stripped = line.rstrip()
                match = re.fullmatch(r"namespace\s+(" + QUALIFIED + r")", stripped)
                if match:
                    scopes.append(("namespace", match.group(1)))
                    continue
                match = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+(" + QUALIFIED + r"))?",
                                     stripped)
                if match:
                    scopes.append(("section", match.group(1) or ""))
                    continue
                match = re.fullmatch(r"end(?:\s+(" + QUALIFIED + r"))?", stripped)
                if match:
                    need(scopes and scopes[-1][1] == (match.group(1) or ""),
                         "unsupported Lean scope end")
                    scopes.pop()
                    continue
                match = DECLARATION.fullmatch(stripped)
                if match:
                    kind, short, header = match.groups()
                    prefix = ".".join(name for scope, name in scopes if scope == "namespace")
                    name = prefix + "." + short if prefix else short
                    need(name not in declarations, "duplicate Lean declaration")
                    current = {"source": source, "kind": kind, "header": header,
                               "namespace": prefix, "fields": [], "types": {},
                               "assignments": {}, "body": None}
                    declarations[name] = current
                continue
            if current is None:
                continue
            if current["kind"] == "structure":
                if not re.search(r"\bwhere\s*$", current["header"]):
                    current["header"] += " " + line.strip()
                    continue
                match = re.match(r"  (" + IDENT + r")\s*:(?!=)(.*)$", line)
                if match:
                    need(match.group(1) not in current["types"], "duplicate Lean structure field")
                    member = match.group(1)
                    current["fields"].append(member)
                    current["types"][member] = match.group(2).strip()
                elif member is not None and re.match(r"   ", line):
                    current["types"][member] += " " + line.strip()
            elif current["kind"] == "theorem":
                if re.fullmatch(r"\s*:\s*(" + QUALIFIED + r")\s+where\s*", current["header"]):
                    match = re.match(r"  (" + IDENT + r")\s*:=\s*(\S.*?)\s*$", line)
                    if match:
                        need(match.group(1) not in current["assignments"],
                             "duplicate Lean certificate field")
                        member = match.group(1)
                        current["assignments"][member] = match.group(2)
                    elif member is not None and re.match(r"   ", line):
                        current["assignments"][member] += " " + line.strip()
                elif re.fullmatch(r"\s*:\s*(" + QUALIFIED + r")\s*:=.*", current["header"]):
                    current["body"] = (current["body"] or "") + " " + line.strip()
        need(all(scope == "section" and not name for scope, name in scopes),
             "unclosed Lean namespace or named section")
    return declarations


def resolve(declarations, namespace, identifier):
    parts = namespace.split(".") if namespace else []
    for i in range(len(parts), -1, -1):
        name = ".".join(parts[:i] + [identifier])
        if name in declarations:
            return name
    return None


def declared_type(item, suffix):
    """The declared type name of a theorem header, or None if the header has another form."""
    match = re.fullmatch(r"\s*:\s*(" + QUALIFIED + r")\s*" + suffix, item["header"])
    return None if match is None else match.group(1)


def prop_structure(declarations, name, source):
    item = declarations.get(name)
    need(item is not None and item["source"] == source and item["kind"] == "structure" and
         re.fullmatch(r"(?:\s*\([^()]*\))*\s*:\s*Prop\s+where\s*", item["header"]) is not None and
         bool(item["fields"]), "missing mapped Lean structure: " + str(name))
    return item


def referenced_proofs(declarations, namespace, value):
    found = set()
    for token in re.findall(r"(?<![\w'.])(" + QUALIFIED + r")", value):
        name = resolve(declarations, namespace, token.rstrip("."))
        if name is not None and declarations[name]["kind"] in PROOF_KINDS:
            found.add(name)
    return sorted(found)


def validate_lean(mapping, sources):
    project = mapping["lean"]
    keys(project, {"root", "declaration", "source", "proposition", "proposition_source",
                   "axiom_probe", "scope"}, "Lean project")
    for key in project:
        string(project[key], "Lean project " + key)
    need(project["root"] == LEAN_ROOT and project["source"] == LEAN_ROOT + "/" + LIBRARY + ".lean"
         and project["axiom_probe"] == AXIOM_PROBE, "Lean project entry points")
    for path in (project["source"], project["proposition_source"], project["axiom_probe"]):
        need(path in sources and path.endswith(".lean"), "missing Lean source")
    declarations = lean_index(sources)
    proposition = prop_structure(declarations, project["proposition"],
                                 project["proposition_source"])
    aggregate = declarations.get(project["declaration"])
    need(aggregate is not None and aggregate["source"] == project["source"] and
         aggregate["kind"] == "theorem", "missing aggregate Lean theorem")
    kind = declared_type(aggregate, r":=.*")
    need(kind is not None and resolve(declarations, aggregate["namespace"], kind) ==
         project["proposition"], "aggregate theorem type")
    body = (re.sub(r"^\s*:\s*" + QUALIFIED + r"\s*:=", "", aggregate["header"]) + " " +
            (aggregate["body"] or "")).strip()
    match = matched(re.fullmatch(r"⟨\s*(" + QUALIFIED + r"(?:\s*,\s*" + QUALIFIED + r")*)\s*,?\s*⟩",
                                 body), "aggregate constructor syntax")
    arguments = [resolve(declarations, aggregate["namespace"], name.strip())
                 for name in match.group(1).split(",")]
    probe = lean_without_comments(sources[project["axiom_probe"]])
    need(re.search(r"^#print axioms " + re.escape(project["declaration"]) + r"\s*$",
                   probe, re.MULTILINE) is not None,
         "axiom probe does not name the aggregate theorem")
    components = mapping["lean_components"]
    need(isinstance(components, list) and
         [c.get("field") if isinstance(c, dict) else None for c in components] ==
         [project["proposition"] + "." + f for f in proposition["fields"]],
         "Lean component list")
    need(len(arguments) == len(components), "aggregate constructor")
    owners, by_id = {}, {}
    for position, item in enumerate(components):
        keys(item, {"id", "field", "structure", "structure_source", "declaration", "source",
                    "scope"}, "Lean component")
        for key in item:
            string(item[key], "Lean component " + key)
        need(item["id"] not in by_id, "duplicate Lean component")
        by_id[item["id"]] = item
        field = item["field"].rpartition(".")[2]
        need(resolve(declarations, proposition["namespace"], proposition["types"][field]) ==
             item["structure"], "component structure type")
        structure = prop_structure(declarations, item["structure"], item["structure_source"])
        proof = declarations.get(item["declaration"])
        need(proof is not None and proof["source"] == item["source"] and
             proof["kind"] == "theorem", "missing component Lean theorem")
        kind = declared_type(proof, r"where\s*")
        need(kind is not None and resolve(declarations, proof["namespace"], kind) ==
             item["structure"], "component theorem type")
        need(set(proof["assignments"]) == set(structure["fields"]),
             "component assignments differ from structure fields")
        need(arguments[position] == item["declaration"], "aggregate constructor")
        owners[item["structure"]] = ("field", item, structure, proof)
    results = mapping["lean_results"]
    need(isinstance(results, list), "Lean results list")
    for item in results:
        keys(item, {"id", "component", "via", "structure", "structure_source", "scope"},
             "Lean result")
        for key in item:
            string(item[key], "Lean result " + key)
        need(item["component"] in by_id and item["structure"] not in owners, "Lean result owner")
        component = by_id[item["component"]]
        owner, _, field = item["via"].rpartition(".")
        need(owner == component["structure"] and field in owners[owner][2]["fields"],
             "result structure binding")
        structure = prop_structure(declarations, item["structure"], item["structure_source"])
        short = item["structure"].rpartition(".")[2]
        conclusion = re.split(r"→", owners[owner][2]["types"][field])[-1].strip()
        need(re.match(re.escape(short) + r"\b", conclusion) is not None,
             "result structure binding")
        owners[item["structure"]] = ("result", item, structure, field)
    expected = {owner + "." + f for owner, record in owners.items() for f in record[2]["fields"]}
    targets, covered = {}, set()
    need(isinstance(mapping["lean_targets"], list), "Lean targets list")
    for item in mapping["lean_targets"]:
        keys(item, {"id", "component", "field", "proofs", "scope"}, "Lean target")
        for key in ("id", "component", "field", "scope"):
            string(item[key], "Lean target " + key)
        strings(item["proofs"], "Lean target proofs")
        need(item["id"] not in targets, "duplicate Lean target")
        targets[item["id"]] = item
        owner, _, field = item["field"].rpartition(".")
        need(owner in owners and field in owners[owner][2]["fields"], "unknown Lean field")
        need(item["field"] not in covered, "duplicate Lean field")
        covered.add(item["field"])
        kind, record = owners[owner][0], owners[owner][1]
        if kind == "field":
            need(item["component"] == record["id"], "Lean target component")
            proof = owners[owner][3]
            value = proof["assignments"][field]
        else:
            need(item["component"] == record["component"], "Lean target component")
            component = by_id[record["component"]]
            proof = owners[component["structure"]][3]
            value = proof["assignments"][owners[owner][3]]
        expected_proofs = referenced_proofs(declarations, proof["namespace"], value)
        if not expected_proofs:
            expected_proofs = [by_id[item["component"]]["declaration"]]
        need(sorted(item["proofs"]) == expected_proofs and item["proofs"] == expected_proofs,
             "Lean target proof mismatch")
        for name in item["proofs"]:
            need(declarations[name]["source"].startswith(LEAN_ROOT + "/"), "Lean proof source")
    need(covered == expected, "unmapped Lean field")
    counts = (sum(1 for t in targets.values() if owners[t["field"].rpartition(".")[0]][0] ==
                  "field"),
              sum(1 for t in targets.values() if owners[t["field"].rpartition(".")[0]][0] ==
                  "result"))
    return targets, counts, len(components), [r["structure"] for r in results]


# ------------------------------------------------------------------ exact checks and numerics

def checker_families(text):
    families, checker = set(), None
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        if not line.startswith(" "):
            checker = line.strip()
        else:
            match = re.fullmatch(r"  (\S+)  \S.*", line)
            if match:
                need(checker is not None, "exact-check family list")
                families.add((checker, match.group(1)))
    return families


def validate_checks(mapping, sources):
    checks = {}
    families = checker_families(sources[CHECKERS_TXT])
    need(isinstance(mapping["exact_checks"], list), "exact checks list")
    for item in mapping["exact_checks"]:
        keys(item, {"id", "family", "source", "function", "scope", "limitation"}, "exact check")
        for key in item:
            string(item[key], "exact check " + key)
        need(item["id"] not in checks, "duplicate exact check")
        checks[item["id"]] = item
        folder, _, name = item["source"].rpartition("/")
        need(item["source"] in sources and folder == EXACT_FOLDER and name in EXACT_CHECKERS,
             "missing exact-check source")
        tree = ast.parse(sources[item["source"]], filename=item["source"])
        functions = [node.name for node in tree.body if isinstance(node, ast.FunctionDef)]
        need(functions.count(item["function"]) == 1, "missing mapped exact-check function")
        need((name, item["family"]) in families, "exact-check family")
    mapped = {(c["source"].rpartition("/")[2], c["family"]) for c in checks.values()}
    need({f for f in families if f[0] in EXACT_CHECKERS} == mapped, "unmapped exact-check family")
    return checks


def validate_numerics(mapping, sources, labels):
    items = {}
    inventory = set(sources[NUMERICS_INVENTORY].split("\n"))
    need(isinstance(mapping["numerics"], list), "numerics list")
    for item in mapping["numerics"]:
        keys(item, {"id", "paper_labels", "files", "scope"}, "numerics item")
        string(item["id"], "numerics id")
        string(item["scope"], "numerics scope")
        strings(item["paper_labels"], "numerics paper labels")
        strings(item["files"], "numerics files")
        need(bool(item["files"]), "numerics files")
        need(item["id"] not in items, "duplicate numerics item")
        items[item["id"]] = item
        for label in item["paper_labels"]:
            need(label in labels and labels[label]["kind"] in FLOATS, "numerics paper label")
        for name in item["files"]:
            safe_path(name)
            need(name in inventory, "missing numerics file")
    return items


# ------------------------------------------------------------------ the mapping

def result_name(row):
    return ENVIRONMENTS[row["environment"]] + " " + row["number"]


def step_name(row):
    if row["kind"] == "equation":
        return "(" + row["number"] + ")"
    return ("Appendix " if row["number"].isalpha() else "Section ") + row["number"]


def result_rows(rows):
    return [TABLE_RULE_5] + [
        "| " + result_name(row) + " | " + ", ".join("`" + x + "`" for x in row["labels"]) +
        " | " + str(row["page"]) + " | " + row["title"] + " | " + COVERAGES[row["coverage"]] +
        " |" for row in rows]


def step_rows(rows):
    return [TABLE_RULE_4] + [
        "| " + step_name(row) + " | `" + row["label"] + "` | " + str(row["page"]) + " | " +
        row["title"] + " |" for row in rows]


def table_block(lines, header):
    need(lines.count(header) == 1, "section table header")
    start = lines.index(header) + 1
    block = []
    while start < len(lines) and lines[start].startswith("|"):
        block.append(lines[start])
        start += 1
    return block


def validate(mapping, sources):
    keys(mapping, {"schema_version", "paper", "pages", "scope", "lean", "lean_components",
                   "lean_results", "lean_targets", "exact_checks", "numerics",
                   "numbered_results", "supporting_steps"}, "mapping")
    need(type(mapping["schema_version"]) is int and mapping["schema_version"] == 1,
         "schema version")
    need(mapping["paper"] == PAPER, "paper entry point")
    positive_int(mapping["pages"], "page count")
    string(mapping["scope"], "mapping scope")
    sections, inventory, labels = paper_index(sources, mapping["paper"])
    targets, counts, components, result_structures = validate_lean(mapping, sources)
    checks = validate_checks(mapping, sources)
    numerics = validate_numerics(mapping, sources, labels)
    used = {"targets": set(), "checks": set(), "numerics": set(), "labels": set()}

    def references(row, label_list):
        string(row["section"], "paper section")
        string(row["source"], "paper source")
        string(row["title"], "result title")
        need("|" not in row["title"] and "`" not in row["title"], "result title characters")
        positive_int(row["page"], "page number")
        need(row["page"] <= mapping["pages"], "page number")
        strings(row["lean_targets"], "Lean references")
        strings(row["exact_checks"], "exact-check references")
        need(set(row["lean_targets"]) <= set(targets), "unknown Lean reference")
        need(set(row["exact_checks"]) <= set(checks), "unknown exact-check reference")
        for label in label_list:
            need(label in labels, "missing mapped paper label")
            need({k: labels[label][k] for k in ("section", "source")} ==
                 {"section": row["section"], "source": row["source"]}, "paper anchor location")
            need(label not in used["labels"], "duplicate mapped paper label")
            used["labels"].add(label)
        used["targets"].update(row["lean_targets"])
        used["checks"].update(row["exact_checks"])
        string(row["covered"], "covered scope")
        string(row["not_covered"], "uncovered scope")

    rows = mapping["numbered_results"]
    need(isinstance(rows, list), "numbered results list")
    row_index, pages, tally = [], [], {key: 0 for key in COVERAGES}
    for row in rows:
        keys(row, {"labels", "environment", "number", "page", "section", "source", "title",
                   "coverage", "lean_targets", "exact_checks", "numerics", "covered",
                   "not_covered"}, "numbered result")
        strings(row["labels"], "paper labels")
        need(bool(row["labels"]), "paper labels")
        references(row, row["labels"])
        need(row["environment"] in ENVIRONMENTS, "result environment")
        string(row["number"], "result number")
        strings(row["numerics"], "numerics references")
        need(set(row["numerics"]) <= set(numerics), "unknown numerics reference")
        used["numerics"].update(row["numerics"])
        need(row["coverage"] in COVERAGES, "unsupported coverage claim")
        formal = row["coverage"] in ("formalized_in_full", "formalized_scalar_part")
        need(formal == bool(row["lean_targets"]), "Lean coverage classification")
        need(row["coverage"] != "exact_cross_check_only" or bool(row["exact_checks"]),
             "empty finite coverage")
        need(row["coverage"] != "written_proof_only" or not row["exact_checks"],
             "exact-check coverage classification")
        tally[row["coverage"]] += 1
        pages.append(row["page"])
        row_index.append({k: row[k] for k in ("environment", "number", "section", "source",
                                              "labels", "title")})
    need(row_index == inventory, "numbered result inventory mismatch")
    need(pages == sorted(pages), "page order")
    steps = mapping["supporting_steps"]
    need(isinstance(steps, list), "supporting steps list")
    for row in steps:
        keys(row, {"label", "kind", "number", "page", "section", "source", "title",
                   "lean_targets", "exact_checks", "covered", "not_covered"}, "supporting step")
        string(row["label"], "supporting step label")
        references(row, [row["label"]])
        need(row["kind"] in ("equation", "section") and
             {"kind": row["kind"], "number": row["number"]} ==
             {k: labels[row["label"]][k] for k in ("kind", "number")}, "supporting step number")
        need(bool(row["lean_targets"]) or bool(row["exact_checks"]), "empty supporting step")
    need(used["targets"] == set(targets), "unreferenced Lean target")
    need(used["checks"] == set(checks), "unreferenced exact check")
    lines = sources[BY_SECTION].splitlines()
    need(table_block(lines, RESULT_HEADER) == result_rows(rows), "section table mismatch")
    need(table_block(lines, STEP_HEADER) == step_rows(steps), "supporting table mismatch")
    text = sources[BY_SECTION]
    for item in targets.values():
        need("`" + item["field"] + "`" in text, "Lean field not described in by-section.md")
    for item in checks.values():
        need("`" + item["source"] + ":" + item["function"] + "`" in text,
             "exact check not described in by-section.md")
    for item in numerics.values():
        for name in item["files"]:
            need("`" + name + "`" in text, "numerics file not described in by-section.md")
    return {"sections": sections, "results": len(inventory), "counts": counts,
            "components": components, "result_structures": result_structures,
            "checks": len(checks), "steps": len(steps), "numerics": len(numerics),
            "tally": tally}


# ------------------------------------------------------------------ negative controls

def negative_controls(mapping, sources):
    cases = []

    def changed(label, mutate, expected):
        bad_mapping, bad_sources = copy.deepcopy(mapping), dict(sources)
        mutate(bad_mapping, bad_sources)
        cases.append((label, bad_mapping, bad_sources, expected))

    def edit(name, old, new, count=1):
        def mutate(m, s):
            need(old in s[name], "negative-control anchor missing: " + name)
            s[name] = s[name].replace(old, new, count)
        return mutate

    def drop(name):
        def mutate(m, s):
            need(name in s, "negative-control anchor missing: " + name)
            del s[name]
        return mutate

    def row(m, label):
        found = [r for r in m["numbered_results"] if r["labels"][0] == label]
        need(len(found) == 1, "negative-control anchor missing: " + label)
        return found[0]

    def step(m, label):
        found = [r for r in m["supporting_steps"] if r["label"] == label]
        need(len(found) == 1, "negative-control anchor missing: " + label)
        return found[0]

    def target(m, ident):
        found = [t for t in m["lean_targets"] if t["id"] == ident]
        need(len(found) == 1, "negative-control anchor missing: " + ident)
        return found[0]

    def check(m, ident):
        found = [c for c in m["exact_checks"] if c["id"] == ident]
        need(len(found) == 1, "negative-control anchor missing: " + ident)
        return found[0]

    def numerics(m, ident):
        found = [c for c in m["numerics"] if c["id"] == ident]
        need(len(found) == 1, "negative-control anchor missing: " + ident)
        return found[0]

    def without_numerics_file(name):
        def mutate(m, s):
            files = s[NUMERICS_INVENTORY].split("\n")
            need(name in files, "negative-control anchor missing: " + name)
            s[NUMERICS_INVENTORY] = "\n".join(f for f in files if f != name)
        return mutate

    endpoint = "lean/KE02/EndpointProof.lean"
    changed("missing paper label",
            lambda m, s: row(m, "thm:main").update(labels=["thm:absent"]),
            "missing mapped paper label")
    changed("omitted numbered result", lambda m, s: m["numbered_results"].pop(),
            "numbered result inventory mismatch")
    changed("duplicate numbered result",
            lambda m, s: m["numbered_results"].append(copy.deepcopy(m["numbered_results"][0])),
            "duplicate mapped paper label")
    changed("wrong result number",
            lambda m, s: row(m, "thm:selection").update(number="4.3"),
            "numbered result inventory mismatch")
    changed("dropped second label",
            lambda m, s: row(m, "lem:defect-contraction").update(labels=["lem:defect-contraction"]),
            "numbered result inventory mismatch")
    changed("wrong result section",
            lambda m, s: row(m, "lem:oracle").update(section="3"),
            "paper anchor location")
    changed("wrong result title",
            lambda m, s: row(m, "lem:oracle").update(title="Spectral oracle"),
            "numbered result inventory mismatch")
    changed("unlabelled numbered result",
            edit(PAPER, r"\end{document}", r"\begin{lemma}[X]X\end{lemma}\end{document}"),
            "numbered result requires a direct label")
    changed("unmapped numbered result",
            edit(PAPER, r"\end{document}",
                 r"\begin{lemma}[X]\label{lem:unmapped}X\end{lemma}\end{document}"),
            "numbered result inventory mismatch")
    changed("shared theorem counter",
            edit(PAPER, r"\newtheorem{lemma}{Lemma}[section]", r"\newtheorem{lemma}[theorem]{Lemma}"),
            "unsupported theorem counter declaration")
    changed("counter modification",
            edit(PAPER, r"\begin{document}", "\\begin{document}\n\\setcounter{equation}{1}"),
            "unsupported paper counter modification")
    changed("unsupported paper inclusion",
            edit(PAPER, r"\input{matrix_with_cut.tex}", r"\input{matrix_with_cut.tex}\relax"),
            "unsupported paper inclusion")
    changed("missing paper input", drop("paper/matrix_with_cut.tex"),
            "missing paper input: paper/matrix_with_cut.tex")
    changed("shifted equation number",
            edit(PAPER, r"\section{Introduction}",
                 "\\section{Introduction}\n\\begin{equation}x\\end{equation}"),
            "supporting step number")
    changed("page order",
            lambda m, s: row(m, "rem:real").update(page=1),
            "page order")
    changed("missing Lean helper theorem",
            edit(endpoint, "theorem endpoint_contraction ", "theorem absent_contraction "),
            "Lean target proof mismatch")
    changed("comment-only Lean helper theorem",
            lambda m, s: s.update({endpoint: "/- theorem endpoint_contraction : True -/\n" +
                                   s[endpoint].replace("theorem endpoint_contraction ",
                                                       "theorem absent_contraction ", 1)}),
            "Lean target proof mismatch")
    changed("missing Lean file", drop("lean/KE02/WronskianProof.lean"),
            "missing component Lean theorem")
    changed("wrong proof of a field",
            lambda m, s: target(m, "endpoint.contraction").update(
                proofs=["KE02.endpoint_children_sum"]),
            "Lean target proof mismatch")
    changed("unmapped Lean field", lambda m, s: m["lean_targets"].pop(),
            "unmapped Lean field")
    changed("changed component structure",
            edit("lean/KE02/EndpointStatement.lean", "  ties_left :",
                 "  extra_field : True\n  ties_left :"),
            "component assignments differ from structure fields")
    changed("reordered aggregate constructor",
            edit("lean/KE02.lean", "⟨endpointCertificate, algorithm2Certificate,",
                 "⟨algorithm2Certificate, endpointCertificate,"),
            "aggregate constructor")
    changed("aggregate constructor syntax",
            edit("lean/KE02.lean", "⟨endpointCertificate, algorithm2Certificate,",
                 "⟨endpointCertificate, (algorithm2Certificate),"),
            "aggregate constructor syntax")
    changed("wrong aggregate type",
            edit("lean/KE02.lean", "theorem coreCertificate : CoreCertificate :=",
                 "theorem coreCertificate : EndpointCertificate :="),
            "aggregate theorem type")
    changed("axiom probe",
            edit(AXIOM_PROBE, "#print axioms KE02.coreCertificate",
                 "#print axioms KE02.endpointCertificate"),
            "axiom probe does not name the aggregate theorem")
    changed("unclosed Lean namespace",
            edit("lean/KE02/WronskianStatement.lean", "\nend KE02", "\n"),
            "unclosed Lean namespace or named section")
    changed("rebound run field",
            edit("lean/KE02/Algorithm2Statement.lean",
                 "    Algorithm2Outcome n δ F O (alg2Run O n δ)",
                 "    True ∧ Algorithm2Outcome n δ F O (alg2Run O n δ)"),
            "result structure binding")
    changed("full formalization claim",
            lambda m, s: row(m, "thm:main").update(coverage="fully_formalized"),
            "unsupported coverage claim")
    changed("formal class without Lean target",
            lambda m, s: row(m, "rem:real").update(coverage="formalized_scalar_part"),
            "Lean coverage classification")
    changed("exact-only result with Lean target",
            lambda m, s: row(m, "lem:convex")["lean_targets"].append("endpoint.centered_nonneg"),
            "Lean coverage classification")
    changed("written-only result with exact check",
            lambda m, s: row(m, "rem:real")["exact_checks"].append("C01"),
            "exact-check coverage classification")
    changed("unknown Lean reference",
            lambda m, s: row(m, "thm:main")["lean_targets"].append("absent"),
            "unknown Lean reference")
    changed("missing exact function",
            lambda m, s: check(m, "C12").update(function="fam_absent"),
            "missing mapped exact-check function")
    changed("missing exact-check file",
            lambda m, s: check(m, "C12").update(source=EXACT_FOLDER + "/check_absent.py"),
            "missing exact-check source")
    changed("unlisted exact-check family",
            lambda m, s: check(m, "C12").update(family="C99"),
            "exact-check family")
    changed("unmapped exact-check family", lambda m, s: m["exact_checks"].pop(),
            "unmapped exact-check family")
    changed("missing numerics file", without_numerics_file("data/adaptive.jsonl"),
            "missing numerics file")
    changed("numerics label of a theorem",
            lambda m, s: numerics(m, "adaptive")["paper_labels"].append("thm:main"),
            "numerics paper label")
    changed("supporting step at a result label",
            lambda m, s: step(m, "eq:wronskian").update(label="lem:localization"),
            "duplicate mapped paper label")
    changed("section table drift", edit(BY_SECTION, "| Theorem 1.1 |", "| Theorem 1.2 |"),
            "section table mismatch")
    changed("supporting table drift", edit(BY_SECTION, "| (43) |", "| (42) |"),
            "supporting table mismatch")
    changed("undescribed Lean field",
            edit(BY_SECTION, "`KE02.EndpointCertificate.contraction`",
                 "`KE02.EndpointCertificate.absent`", -1),
            "Lean field not described in by-section.md")
    changed("undescribed exact check",
            edit(BY_SECTION, "`verification/core/check_constants.py:fam_c12`",
                 "`verification/core/check_constants.py:fam_absent`", -1),
            "exact check not described in by-section.md")
    for label, bad_mapping, bad_sources, expected in cases:
        try:
            validate(bad_mapping, bad_sources)
        except SystemExit as error:
            need(str(error) == "FAIL: " + expected, "wrong negative-control rejection: " + label)
        else:
            raise SystemExit("FAIL: accepted negative control: " + label)
    json_cases = (('{"schema_version":1,"schema_version":1}', "duplicate JSON key"),
                  ('{"schema_version":1.0}', "unsupported JSON number"))
    for text, expected in json_cases:
        try:
            parse_json(text)
        except SystemExit as error:
            need(str(error) == "FAIL: " + expected, "wrong JSON rejection: " + expected)
        else:
            raise SystemExit("FAIL: accepted JSON control: " + expected)
    return len(cases) + len(json_cases)


def main():
    need(len(sys.argv) == 1, "this command takes no arguments")
    sources = read_inputs()
    mapping = parse_json(sources[MAPPING])
    summary = validate(mapping, sources)
    controls = negative_controls(mapping, sources)
    need(read_inputs() == sources, "sources changed during check")
    sections = summary["sections"]
    numbered = sum(1 for s in sections if not s["number"].isalpha())
    lettered = [s["number"] for s in sections if s["number"].isalpha()]
    print("PASS: " + str(summary["results"]) + " numbered results in " + str(numbered) +
          " numbered sections and appendix " + ", ".join(lettered) + ", in TeX order")
    fields, results = summary["counts"]
    print("PASS: " + str(fields + results) + " Lean fields mapped to their proofs: " +
          str(fields) + " fields of the " + str(summary["components"]) +
          " components of KE02.CoreCertificate and " + str(results) + " fields of " +
          ", ".join(summary["result_structures"]))
    print("PASS: " + str(summary["checks"]) + " exact-check families, " + str(summary["steps"]) +
          " supporting paper anchors and " + str(summary["numerics"]) + " numerics items")
    print("PASS: by-section.md tables and references match the mapping")
    print("PASS: coverage: " + ", ".join(str(summary["tally"][key]) + " " +
                                          COVERAGES[key].lower() for key in COVERAGES))
    print("PASS: " + str(controls) + " mapping negative controls rejected")
    print("RESULT: PASS mapping structure; mathematical coverage is stated per entry")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, IndexError, AttributeError,
            SyntaxError, UnicodeError, RecursionError) as error:
        raise SystemExit("FAIL: mapping input: " + type(error).__name__)
