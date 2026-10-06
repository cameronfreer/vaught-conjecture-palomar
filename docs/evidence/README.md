# Reference prototype evidence, not an extraction build receipt

These small receipts come from the reference worktree's local run
`.lake/audit/palomar-prototype/run.iMhyXk` on 2026-10-06. The source base was
`57d74cd8309696d242614aeaede028e56321cfe3`; the prototype files were additional
uncommitted files, individually recorded in the SHA256 receipt. Paths in that
receipt are reference-project paths, not paths in this repository.

The run exited zero after strict Solution compilation, transitive standard-axiom
checking, rejection of a wrong statement and of the unproved Challenge as a
Solution, Comparator matching, NanoDa acceptance, Lean default-kernel acceptance,
and source-hash stability. Built dependency artifacts from the reference were
used. This was neither a clean build nor the Palomar reusable workflow.

The Challenge and Solution copied here initially have exactly those checked bytes.
Future module conversion changes require a new replay; this receipt does not
certify subsequent revisions. Large exports and build artifacts remain outside
Git in the reference worktree. The local driver was subsequently hardened to
fail explicitly on dependency-list parsing errors, without changing Lean sources.
