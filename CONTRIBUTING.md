# Contributing to Functional Algorithm Design

This guide helps you contribute to `FAD`, which translates into Lean and
formalizes the algorithms of the book *Algorithm Design with Haskell*.

## Step by step

### Open an issue

Before you start coding, open an *issue* describing your proposal.

- Kinds of contribution:
  - Implementing a data structure or an algorithm
  - Proving properties
  - Fixing bugs (uses of `sorry`, failures, etc.)
  - Refactoring or other improvements

- How to open one:
  1. Go to *Issues* on GitHub.
  2. Click *New Issue*.
  3. Give it a clear, descriptive title.
  4. In the body, explain:
     - which section or chapter of the book it covers;
     - what will be implemented, formalized or fixed;
     - for a bug, how to reproduce it.

Wait for feedback before you start working on it.

### Clone the repository

In a terminal:

```bash
git clone https://github.com/cslib-community/fad.git
cd fad
```

You only need to clone the repository once. After that, repeat the steps
below for each contribution.

### Create a branch

Update your copy of the main branch and create a new branch for your
contribution:

```bash
git checkout main
git pull origin main
git checkout -b issue-XX  # replace XX with the number of your issue
```

### Make your changes and commit

Add the files you changed and commit them with clear messages:

```bash
git add path/to/your_file.lean
git commit -m "issue-XX: clear description of the change"
```

*Tip:* small commits are easier to review.

### Push your branch

```bash
git push origin issue-XX
```

### Open a pull request (PR)

On GitHub:

1. Click *Compare & pull request*, or create a new PR by hand.
2. Set:
   - base: `main`
   - compare: `issue-XX`
3. In the body of the PR:
   - describe the changes;
   - write `Closes #XX` to link the issue;
   - explain any relevant details.

### Wait for review

- Your PR will be reviewed with comments and suggestions.
- Push new commits to the same branch to update it.
- Once approved, it will be merged into `main`.

## Lean files: the module system

Every file in the `Fad` library uses Lean's
[module system](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).
A new file should start like this:

```lean
module

public import Fad.Chapter1
public import Mathlib.Tactic

@[expose] public section

namespace ChapterXX
```

- `module` must be the first command in the file.
- Use `public import` for imports.
- `@[expose] public section` makes declarations public and keeps the
  bodies of definitions visible to other files, for `rfl`, `simp [f]`,
  `decide` and `#eval`. Without `@[expose]`, other chapters cannot unfold
  your definitions.
- Add the new file to `Fad.lean` with `public import`.

To convert an old file, run `python3 scripts/to_modules.py` from the root
of the repository.

### Pitfalls

- `#eval` only runs code from *another* file if that file is also imported
  with `meta import Fad.ChapterXX`. Prefer checking the result with
  `example : f x = y := rfl`, which does not need it and also works as a
  test.
- A recursive definition with `let rec` (or `where`) that captures
  parameters of the outer definition may fail the termination check if it
  uses `by` proofs inside the recursive body. Use term proofs there (for
  example `List.cons_ne_nil _ _` instead of `by simp`). See
  [lean4#10721](https://github.com/leanprover/lean4/issues/10721).
- Some functions in the standard library do not expose their bodies, so
  `simp [List.scanr]` does not work; use the equation lemmas
  (`List.scanr_nil`, `List.scanr_cons`) instead.

## General good practices

- Always start with an *issue*.
- Use clear titles and descriptions.
- Keep commits small and focused.
- Keep your branch up to date with `main`:

```bash
git checkout main
git pull origin main
git checkout BRANCH_NAME
git merge main  # brings updates from main into the current branch
```

## Commit messages

Write clear, concise commit messages in the imperative mood, following
the convention below.

### Recommended format

```
<type>(optional scope): short description in the imperative

Optional body explaining what changed and why.

Optional footer: references to issues, breaking changes, etc.
```

### Example

```
feat(list): add an implementation of linked lists

Based on section 2.3 of the book.
Includes ordered insertion.

Closes #42
```

### Common types (prefixes)

- `feat`: new functionality
- `fix`: bug fix
- `docs`: documentation changes
- `style`: formatting changes (no change in meaning)
- `refactor`: refactoring without changing behaviour
- `test`: tests added or changed
- `chore`: maintenance tasks (CI, configuration)

### Main rules

- Use the imperative: *"add support"*, not *"adding support"*.
- Keep the first line under 50 characters.
- Separate the body from the first line with a blank line.
- Explain *why*, not only *what*.

If you have questions, ask the maintainers. Happy contributing!
