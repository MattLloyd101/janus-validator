## Coq proofs workspace

This directory is intentionally **separate** from the TypeScript build. It’s a place to
formalize and mechanically check soundness properties of the domain implementations.

### What’s here (so far)

- **`theories/JanusProofs/FiniteDomain.v`**: starter development showing that finite-domain membership is decidable
  and that a boolean membership function is correct (via `reflect`).
- **`_RocqProject`**: Rocq project file (Rocq is the new name for Coq).
- **`_CoqProject`**: kept for compatibility with older tooling/editors.
- **`Makefile`**: build wrapper that prefers `rocqmakefile` (and falls back to `coq_makefile`).

### Install Rocq (recommended via opam)

We don’t vendor Rocq into this repo. The most common setup is `opam`:

- Install `opam` for your platform.
- Run the repo-provided setup target (recommended):

```bash
cd proofs
make setup
eval $(opam env --switch janus-proofs)
```

Notes:
- `make setup` creates an opam switch (default: `janus-proofs`) and installs:
  - Coq (default: `coq.8.18.0`)
  - `coq-lsp` (for VS Code Coq LSP)
  - `dune` + `melange` (for OCaml → JS compilation)
- You can override versions if needed, e.g. `make setup COQ_VERSION=8.18.0 OCAML_VERSION=4.14.1`.
- Depending on your installation, the makefile generator command may be `rocqmakefile` or `coq_makefile`.

### Build

From this `proofs/` directory:

```bash
make
```

To clean:

```bash
make clean
```

### Extract OCaml (`FiniteDomain.ml`)

Extraction is configured at the bottom of `theories/JanusProofs/FiniteDomain.v`.

To run just the extraction compile in one shot:

```bash
cd proofs
make extract
```

This writes **`proofs/FiniteDomain.ml`** (and usually **`proofs/FiniteDomain.mli`**).

### Compile extracted OCaml to JavaScript with Melange

Then from `proofs/`:

```bash
make melange
```

The generated JavaScript will be under:
- `proofs/_build/default/js/` (plus Melange runtime files as needed)

### “Extract to TypeScript” (what’s realistic)

Rocq/Coq extraction is **supported to OCaml** (and a few other languages), but there is **no
first-class TypeScript extraction target**.

What we *can* do (and is common in practice):

- **Extract to OCaml** (supported). Extraction is configured at the bottom of
  `theories/JanusProofs/FiniteDomain.v` and writes to `proofs/extracted/`.
- Then integrate with TypeScript by either:
  - compiling OCaml → **JavaScript** (e.g. `js_of_ocaml`) and wrapping it with TS types, or
  - compiling OCaml → **Wasm** and calling it from Node/browser with a TS wrapper.

Once Rocq is installed, running `make` will also run the extraction step (it’s just another `.v` file).

### TypeScript-idiomatic API (arrays) via a Melange adapter

The extracted core (`extracted/FiniteDomain.ml`) operates on OCaml lists, which are compiled to
linked-list structures in JS. That’s correct but awkward to consume from TS.

To make it ergonomic, we include an adapter module:
- `extracted/FiniteDomain_ts.ml`: exposes domains as **JS arrays** and converts to/from the verified core.

After `make melange`, look for:
- `proofs/_build/default/js/extracted/FiniteDomain_ts.js`

### Next steps (suggested)

- Model `FiniteDomain` more faithfully (e.g. normalized list with no duplicates, and operations
  corresponding to `union`/`intersection`/`difference`).
- Add a “spec vs implementation” structure:
  - `mem : T -> Prop` as the spec
  - `isDefinedAt : T -> bool` as the decision procedure
  - theorems connecting them (`reflect` / equivalences)
- Once you reintroduce generators: prove generator **soundness** (“generated values are always in the domain”).


