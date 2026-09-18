# public

Ephemeral public GitHub Actions runner scratchpad.

This repository intentionally contains no research source code, model outputs, experimental results, or protocol notes.

Normal state: README only.

When compute is needed, a trusted agent temporarily adds a thin workflow that:
1. checks out `hubugui1111-lab/tda-ppml-research` READ ONLY using a repository-scoped Actions secret;
2. runs the private experiment on a standard public GitHub-hosted runner;
3. uploads only small result files as a short-lived artifact;
4. is deleted after the controlling AI imports those results back into the private repository.

Do not copy research source code into public commits.
Do not give the public runner write access to the private research repository merely for convenience.

Canonical instructions live in the private repository's root `AGENTS.md`.
