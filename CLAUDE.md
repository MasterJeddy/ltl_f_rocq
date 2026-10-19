# Instructions for AI assistants working in this repository

This is university coursework (a Coq formalization project). The author must be able
to disclose exactly what AI assistance was used, so **every substantive interaction
must be logged**.

## Logging requirement

After each response that gives the user a proof, code, a fix, or non-trivial technical
guidance, append an entry to `AI_USAGE_LOG.md` in this directory (create it if it does
not exist) with:

- The user's prompt, verbatim.
- A concise but accurate summary of what was answered/produced — including the key
  code, lemma names, or tactics given, not just a vague description.

Follow the existing entry format in `AI_USAGE_LOG.md` (`## Entry N`, `**Prompt:**`,
`**Response summary:**`). Number entries sequentially — do not renumber or edit past
entries. Only append.

Do not skip logging just because the user didn't explicitly ask for it this turn — this
is a standing instruction for the remainder of the project, across sessions.

Purely conversational exchanges that produce no proof/code/technical content (e.g.
clarifying questions, small talk) do not need a log entry.

## Other notes

- Unless explicitly asked to, do not directly edit the `.v` files — the author wants to
  type the Coq proofs themselves so the work is genuinely theirs; give guidance and
  code snippets in chat instead.
