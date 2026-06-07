// review.workflow.js — Layer-2 Claude Code Workflow orchestrator for the
// adversarial Lean code-review harness.
//
// This script runs inside the Claude Code Workflow tool (NOT under `node`). It
// is a thin driver over the Layer-1 assets:
//   - review/worklist.py            (resolve file -> chapter metadata + decls)
//   - review/rubric.md              (authoritative review rubric)
//   - review/prompts/reviewer.md    (adversarial reviewer prompt)
//   - review/prompts/verifier.md    (false-positive-killing verifier prompt)
//   - review/prompts/fixer.md       (mechanical-only fixer prompt)
//   - review/finding-schema.json    (the finding JSON shape)
//
// The orchestrator coordinates only; all file IO and shell (uv, rg, lake) is
// done by the subagents via their own tools. The Workflow harness forbids
// Date.now()/Math.random()/new Date() and any direct Node/filesystem API here,
// so the worklist must be resolved by dispatching an agent that runs
// `uv run review/worklist.py resolve <files...>`.

export const meta = {
  name: "Lean review harness",
  description:
    "Adversarial multi-agent review of Lean files: worklist -> review -> verify -> dedup -> report -> draft mechanical fixes.",
  phases: [
    { title: "Worklist" },
    { title: "Review" },
    { title: "Verify" },
    { title: "Dedup" },
    { title: "Report" },
    { title: "Draft fixes" },
  ],
};

// ---------------------------------------------------------------------------
// JSON schemas the agents must return. These mirror review/finding-schema.json
// (the reviewer emits an array of those objects, wrapped in {findings: [...]}).
// ---------------------------------------------------------------------------

// A single finding, mirroring review/finding-schema.json.
const FINDING_SCHEMA = {
  type: "object",
  additionalProperties: false,
  required: [
    "id", "file", "line", "decl", "dimension", "severity",
    "rule", "claim", "evidence", "suggested_fix", "mechanical", "confidence",
  ],
  properties: {
    id: { type: "string" },
    file: { type: "string" },
    line: { type: "integer", minimum: 1 },
    decl: { type: "string" },
    dimension: { enum: ["redundancy", "hygiene", "faithfulness", "proof-quality"] },
    severity: { enum: ["blocker", "major", "minor", "nit"] },
    rule: { type: "string" },
    claim: { type: "string" },
    evidence: { type: "string" },
    suggested_fix: { type: "string" },
    mechanical: { type: "boolean" },
    confidence: { enum: ["high", "medium", "low"] },
  },
};

// The reviewer returns {findings: [<finding>, ...]}.
const REVIEW_SCHEMA = {
  type: "object",
  additionalProperties: false,
  required: ["findings"],
  properties: {
    findings: { type: "array", items: FINDING_SCHEMA },
  },
};

// One worklist entry per resolved file.
const WORKLIST_SCHEMA = {
  type: "array",
  items: {
    type: "object",
    required: ["file", "chapter", "excerpt_path", "inventory_path", "decls"],
    properties: {
      file: { type: "string" },
      chapter: {}, // integer or null
      excerpt_path: {}, // string or null
      inventory_path: {}, // string or null
      decls: { type: "array" },
    },
  },
};

// The verifier returns a verdict object.
const VERDICT_SCHEMA = {
  type: "object",
  additionalProperties: false,
  required: ["verdict", "reason", "evidence"],
  properties: {
    verdict: { enum: ["confirmed", "refuted"] },
    reason: { type: "string" },
    evidence: { type: "string" },
  },
};

// The four review dimensions, reviewed independently per file.
const DIMENSIONS = ["redundancy", "hygiene", "faithfulness", "proof-quality"];

// Severity ordering for sorting and dedup (higher index == more severe).
const SEVERITY_RANK = { nit: 0, minor: 1, major: 2, blocker: 3 };

// ---------------------------------------------------------------------------
// Phase 1 — Worklist
//
// The orchestrator cannot run uv itself, so dispatch ONE agent to run
// `uv run review/worklist.py resolve <files...>` and return the parsed array.
// ---------------------------------------------------------------------------

phase("Worklist");
const targets = (args || []).filter(Boolean);
log(`Resolving worklist for ${targets.length} file(s).`);

const worklist = await agent(
  [
    "You resolve a review worklist. Using your Bash tool, run exactly:",
    "",
    `    uv run review/worklist.py resolve ${targets.join(" ")}`,
    "",
    "from the repository root. The command prints a JSON array to stdout, one",
    "entry per file with fields {file, chapter, excerpt_path, inventory_path,",
    "decls}. Parse that stdout and return it verbatim as the structured result.",
    "Do not invent entries; return exactly what review/worklist.py emits.",
  ].join("\n"),
  { label: "worklist", phase: "Worklist", schema: WORKLIST_SCHEMA },
);

if (!worklist || worklist.length === 0) {
  log("Worklist is empty; nothing to review.");
  return "# Lean Review Report\n\nNo files resolved; nothing to review.\n";
}

// Build the (file, dimension) work items: agent count is files x 4.
const reviewItems = [];
for (const entry of worklist) {
  for (const dimension of DIMENSIONS) {
    reviewItems.push({ entry, dimension });
  }
}
log(`Built ${reviewItems.length} (file, dimension) review items.`);

// ---------------------------------------------------------------------------
// Phases 2 & 3 — Review then Verify, as an independent per-item pipeline.
//
// Stage 1 (Review): a reviewer agent reads review/prompts/reviewer.md and
//   review/rubric.md and emits {findings: [...]} for one (file, dimension).
// Stage 2 (Verify): each finding is verified by a verifier agent that reads
//   review/prompts/verifier.md; we keep only verdict === "confirmed". The
//   per-finding verifier fan-out runs concurrently with parallel().
// ---------------------------------------------------------------------------

const pipelineResults = await pipeline(
  reviewItems,

  // ----- Stage 1: Review -----
  async (_prev, item) => {
    if (budget.remaining() <= 0) {
      log("Budget exhausted; skipping review stage.");
      return { item, findings: [] };
    }
    const { entry, dimension } = item;
    const reviewer = await agent(
      [
        "You are an adversarial Lean code reviewer for ONE file on ONE dimension.",
        "First read review/prompts/reviewer.md (your full instructions) and the",
        `${dimension} section of review/rubric.md. Emit only findings that conform`,
        "to review/finding-schema.json.",
        "",
        `Target file:    ${entry.file}`,
        `Dimension:      ${dimension}`,
        `Excerpt path:   ${entry.excerpt_path || "(none — not a chapter file)"}`,
        `Inventory path: ${entry.inventory_path || "(none — not a chapter file)"}`,
        "",
        "Declarations (JSON, fields name/line/private):",
        JSON.stringify(entry.decls),
        "",
        "Read the target file in full, gather concrete evidence (prefer the Lean",
        "LSP/leansearch/loogle tools, fall back to `rg`), apply the rubric's",
        '"Does NOT count" filter, and compute each id as',
        "sha1(file:line:decl:dimension).",
        "",
        'Return an object {"findings": [ ...finding objects... ]}; use an empty',
        "array if there are no findings for this dimension.",
      ].join("\n"),
      {
        label: `review:${dimension}:${entry.file}`,
        phase: "Review",
        schema: REVIEW_SCHEMA,
      },
    );
    const findings = (reviewer && reviewer.findings) || [];
    log(`Reviewed ${entry.file} [${dimension}]: ${findings.length} candidate(s).`);
    return { item, findings };
  },

  // ----- Stage 2: Verify -----
  async (prev) => {
    const { item, findings } = prev;
    if (!findings || findings.length === 0) {
      return { item, confirmed: [] };
    }
    if (budget.remaining() <= 0) {
      log("Budget exhausted; skipping verify stage.");
      return { item, confirmed: [] };
    }
    // Fan out one verifier per candidate finding, concurrently with a barrier.
    const verdicts = await parallel(
      findings.map((finding) => async () => {
        const verdict = await agent(
          [
            "You are an adversarial verifier and false-positive killer. Read",
            "review/prompts/verifier.md for your full instructions; your default",
            "posture is to refute, and you default to refuted when uncertain.",
            "Verify exactly this single finding (JSON conforming to",
            "review/finding-schema.json):",
            "",
            JSON.stringify(finding),
            "",
            'Return {"verdict": "confirmed"|"refuted", "reason": ..., "evidence": ...}.',
          ].join("\n"),
          {
            label: `verify:${finding.id}`,
            phase: "Verify",
            schema: VERDICT_SCHEMA,
          },
        );
        // Keep the verifier's gathered evidence on the finding (the fixer's
        // "remove duplicate" edit relies on the verifier's caller analysis).
        if (verdict && verdict.verdict === "confirmed") {
          return {
            ...finding,
            evidence: verdict.evidence || finding.evidence,
          };
        }
        return null; // refuted, uncertain, or failed agent
      }),
    );
    const confirmed = verdicts.filter(Boolean);
    log(`Verified ${item.entry.file} [${item.dimension}]: ${confirmed.length} confirmed.`);
    return { item, confirmed };
  },
);

// ---------------------------------------------------------------------------
// Phase 4 — Dedup
//
// Flatten confirmed findings across every (file, dimension) pipeline and dedup
// by id, keeping the higher severity and unioning evidence.
// ---------------------------------------------------------------------------

phase("Dedup");
const allConfirmed = [];
for (const r of pipelineResults) {
  if (r && r.confirmed) allConfirmed.push(...r.confirmed);
}

const byId = new Map();
for (const f of allConfirmed) {
  const existing = byId.get(f.id);
  if (!existing) {
    byId.set(f.id, { ...f });
    continue;
  }
  // Keep the higher severity.
  if (SEVERITY_RANK[f.severity] > SEVERITY_RANK[existing.severity]) {
    existing.severity = f.severity;
  }
  // Union evidence (dedupe identical strings).
  if (f.evidence && !existing.evidence.includes(f.evidence)) {
    existing.evidence = `${existing.evidence}\n---\n${f.evidence}`;
  }
}
const findings = [...byId.values()];
log(`Deduped to ${findings.length} unique confirmed finding(s).`);

// ---------------------------------------------------------------------------
// Phase 5 — Report
//
// Build a markdown report grouped by file then dimension, severity-sorted.
// The script can't read the clock, so it returns the string; the caller writes
// it to review/reports/<date>-<scope>.md.
// ---------------------------------------------------------------------------

phase("Report");

function groupBy(items, keyFn) {
  const m = new Map();
  for (const it of items) {
    const k = keyFn(it);
    if (!m.has(k)) m.set(k, []);
    m.get(k).push(it);
  }
  return m;
}

const lines = ["# Lean Review Report", ""];
lines.push(`Reviewed ${worklist.length} file(s); ${findings.length} confirmed finding(s).`);
lines.push("");

const byFile = groupBy(findings, (f) => f.file);
for (const file of [...byFile.keys()].sort()) {
  lines.push(`## ${file}`);
  lines.push("");
  const byDim = groupBy(byFile.get(file), (f) => f.dimension);
  for (const dim of DIMENSIONS) {
    const group = byDim.get(dim);
    if (!group || group.length === 0) continue;
    lines.push(`### ${dim}`);
    lines.push("");
    // Severity-sort: most severe first.
    group.sort((a, b) => SEVERITY_RANK[b.severity] - SEVERITY_RANK[a.severity]);
    for (const f of group) {
      lines.push(`- **[${f.severity}]** \`${f.decl}\` (line ${f.line}) — ${f.claim}`);
      lines.push(`  - rule: ${f.rule}`);
      lines.push(`  - evidence: ${f.evidence}`);
      lines.push(`  - suggested fix: ${f.suggested_fix}`);
      lines.push(`  - mechanical: ${f.mechanical} | confidence: ${f.confidence}`);
    }
    lines.push("");
  }
}

if (findings.length === 0) {
  lines.push("No confirmed findings.");
  lines.push("");
}

const report = lines.join("\n");

// ---------------------------------------------------------------------------
// Phase 6 — Draft fixes
//
// Filter confirmed findings to mechanical === true, group per file, and for
// each per-file group dispatch a fixer agent in an isolated git worktree that
// reads review/prompts/fixer.md, applies the edit, and runs `lake build`.
// The fixer fan-out runs via parallel().
// ---------------------------------------------------------------------------

phase("Draft fixes");
const mechanical = findings.filter((f) => f.mechanical === true);
log(`${mechanical.length} mechanical finding(s) eligible for draft fixes.`);

let fixResults = [];
if (mechanical.length > 0 && budget.remaining() > 0) {
  const byFixFile = groupBy(mechanical, (f) => f.file);
  const fixerThunks = [...byFixFile.entries()].map(([file, group]) => async () => {
    return agent(
      [
        "You are a mechanical fixer running in an ISOLATED git worktree. Read",
        "review/prompts/fixer.md for your full instructions: apply ONLY the",
        "narrow, pre-approved mechanical edits, then run `lake build`, and",
        "revert + downgrade to report-only if the build is not green. Never edit",
        "more than the single target file per finding.",
        "",
        `Target file: ${file}`,
        "Confirmed mechanical findings (each conforms to review/finding-schema.json):",
        JSON.stringify(group),
        "",
        "Apply each finding's mechanical edit, rebuild, and report the outcome",
        "per finding (applied or report_only).",
      ].join("\n"),
      {
        label: `fix:${file}`,
        phase: "Draft fixes",
        isolation: "worktree", // draft-PR fixers run isolated
        agentType: "fixer",
      },
    );
  });
  fixResults = (await parallel(fixerThunks)).filter(Boolean);
  log(`Dispatched ${fixerThunks.length} fixer worktree(s); ${fixResults.length} returned.`);
} else {
  log("No mechanical fixes to draft (or budget exhausted).");
}

// The workflow returns the markdown report; the caller persists it under
// review/reports/<date>-<scope>.md (the script cannot read the clock).
return report;
