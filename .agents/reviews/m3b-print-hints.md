# M3B print-hint review

2026-09-25. Independent read-only AI cross-review by two OpenAI Codex
GPT-6 Astra agents. Each excluded its own authored files: the oracle
author reviewed the alternation port and policy validator; the policy
validator author reviewed the printer, dispatch and oracle. Both reviewed
the root's generator/interpreter integration. Alternation was authored
by OpenAI Codex GPT-6 Sol.

No unresolved blocking code findings. Cursor advancement, empty-document
spacing, fusion order, first-hint selection and latest-entry replacement
match upstream. Tables are literal closed data, with no runtime parsing.
Policy lookup retains type-family identity. UTF-8 byte escaping and
ASCII-only lowercasing fix discrepancies observed with the actual pinned
printer. Printer errors become `Fail.err` in generated and interpreted
calls; errors in unused hinted arguments are not propagated.

Findings and disposition:

- Medium: ordinary CI accepted an oracle revision of any 40-character
  string. Fixed: the executable checks the recorded revision against the
  current upstream HEAD. Positive and negative comparison guards added.
- Add selected unprintable-value/error-kind regressions. Fixed at
  printer, builtin and interpreter levels; the interpreter must return
  `Fail.err`. All oracle cases now test these three paths, including an
  unused unprintable argument.
- Refresh the old hint-free Unparse introduction. Fixed.

Independent checks passed in Nix: Alter tests, PrintPolicies tests with
emitted-table elaboration, twelve oracle outputs, and upstream oracle
regeneration `--check`. The 190-entry full-P4 table also elaborated and
matched decoded policies after region erasure. Parent full gate passed,
exit 0, including the added pin and printer-error regressions.

Claim boundaries remain explicit: checked static note changes do not
establish preservation of arbitrary decoded input provenance. Current
note-erasing `Rel`, hint-erasing quotations and `HoldsSpec` do not prove
hinted-print refinement; builtin calls remain outside that fragment.
