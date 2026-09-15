

# Functional Algorithms Design <a href='#'><img src="img/cover.jpeg" align="right" height="168" /></a>

[![Build and Deploy Documentation](https://github.com/arademaker/fad/actions/workflows/docs.yaml/badge.svg)](https://github.com/arademaker/fad/actions/workflows/docs.yml)
[![Lean Version](https://img.shields.io/badge/Lean-4.20.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-✓-green)](https://github.com/leanprover-community/mathlib4)

> *"Algorithm design meets formal verification"*

## Introduction

This [Lean](https://lean-lang.org/) adaptation of [Algorithm Design with Haskell](https://www.cs.ox.ac.uk/publications/books/adwh/) reinterprets five essential principles of algorithm design—divide and conquer, greedy algorithms, thinning, dynamic programming, and exhaustive search—within a dependently typed setting. All examples are reimplemented in Lean, a functional language and proof assistant based on dependent type theory. More than a translation, this version makes explicit the informal equational reasoning of the original by turning it into fully formal, machine-checked proofs.

The main goals of this adaptation are:

- to demonstrate the expressive power of dependent types in reasoning about algorithms,
- to show how informal proofs can be systematically formalized,
- to explore how different refinements of the same algorithm can be proven equivalent.
- and to explore how to prove termination of functional algorithms.

Along the way, readers gain experience not only in algorithm design, but also in writing correct-by-construction programs and proving their properties rigorously. This book invites students and practitioners to see algorithmics not just as a matter of clever ideas, but also as a foundation for precise, verifiable software.

## Table of Contents

### Part One: Basics

1.  Functional programming

    - [x] 1.1 Basic types and functions
    - [x] 1.2 Processing lists
    - [x] 1.3 Inductive and recursive definitions
    - [x] 1.4 Fusion
    - [x] 1.5 Accumulating and tupling
    - [x] Exercises

2.  Timing

    - [ ] 2.1 Asymptotic notation
    - [ ] 2.2 Estimating running times
    - [ ] 2.3 Running times in context
    - [ ] 2.4 Amortised running times
    - [ ] Exercises

3.  Useful data structures

    - [x] 3.1 Symmetric lists
    - [x] 3.2 Random-access lists
    - [x] 3.3 Arrays
    - [ ] Exercises

### Part Two: Divide And Conquer

1.  Binary search

    - [x] 4.1 A one‑dimensional search problem
    - [x] 4.2 A two‑dimensional search problem
    - [x] 4.3 Binary search trees
    - [x] 4.4 Dynamic sets
    - [ ] Exercises

2.  Sorting

    - [x] 5.1 Quicksort
    - [x] 5.2 Mergesort
    - [x] 5.3 Heapsort
    - [x] 5.4 Bucketsort and Radixsort
    - [x] 5.5 Sorting sums
    - [ ] Exercises

3.  Selection

    - [x] 6.1 Minimum and maximum
    - [x] 6.2 Selection from one set
    - [x] 6.3 Selection from two sets
    - [x] 6.4 Selection from the complement of a set
    - [ ] Exercises

### Part Three: Greedy Algorithms

1.  Greedy algorithms on lists

    - [x] 7.1 A generic greedy algorithm
    - [x] 7.2 Greedy sorting algorithms
    - [x] 7.3 Coin‑changing
    - [ ] 7.4 Decimal fractions in TeX
    - [ ] 7.5 Nondeterministic functions and refinement
    - [ ] Exercises

2.  Greedy algorithms on trees

    - [x] 8.1 Minimum‑height trees
    - [x] 8.2 Huffman coding trees
    - [x] 8.3 Priority queues
    - [ ] Exercises

3.  Greedy algorithms on graphs

    - [ ] 9.1 Graphs and spanning trees
    - [ ] 9.2 Kruskal\'s algorithm
    - [ ] 9.3 Disjoint sets and the union--find algorithm
    - [ ] 9.4 Prim\'s algorithm
    - [ ] 9.5 Single‑source shortest paths
    - [ ] 9.6 Dijkstra\'s algorithm
    - [ ] 9.7 The jogger\'s problem
    - [ ] Exercises

### Part Four: Thinning Algorithms

1.  Introduction to thinning

    - [x] 10.1 Theory
    - [x] 10.2 Paths in a layered network
    - [x] 10.3 Coin‑changing revisited
    - [x] 10.4 The knapsack problem
    - [x] 10.5 A general thinning algorithm
    - [ ] Exercises

2.  Segments and subsequences

    - [ ] 11.1 The longest upsequence
    - [ ] 11.2 The longest common subsequence
    - [ ] 11.3 A short segment with maximum sum
    - [ ] Exercises

3.  Partitions

    - [x] 12.1 Ways of generating partitions
    - [ ] 12.2 Managing two bank accounts
    - [x] 12.3 The paragraph problem
    - [ ] Exercises

### Part Five: Dynamic Programming

1.  Efficient recursions

    - [x] 13.1 Two numeric examples
    - [ ] 13.2 Knapsack revisited
    - [ ] 13.3 Minimum‑cost edit sequences
    - [ ] 13.4 Longest common subsequence revisited
    - [ ] 13.5 The shuttle‑bus problem
    - [ ] Exercises

2.  Optimum bracketing

    - [ ] 14.1 A cubic‑time algorithm
    - [ ] 14.2 A quadratic‑time algorithm
    - [ ] 14.3 Examples
    - [ ] 14.4 Proof of monotonicity
    - [ ] 14.5 Optimum binary search trees
    - [ ] 14.6 The Garsia--Wachs algorithm
    - [ ] Exercises

## Part Six: Exhaustive Search

1.  Ways of searching

    - [ ] 15.1 Implicit search and the n‑queens problem
    - [ ] 15.2 Expressions with a given sum
    - [ ] 15.3 Depth‑first and breadth‑first search
    - [ ] 15.4 Lunar Landing
    - [ ] 15.5 Forward planning
    - [ ] 15.6 Rush Hour
    - [ ] Exercises

2.  Heuristic search

    - [ ] 16.1 Searching with an optimistic heuristic
    - [ ] 16.2 Searching with a monotonic heuristic
    - [ ] 16.3 Navigating a warehouse
    - [ ] 16.4 The 8‑puzzle
    - [ ] Exercises


## :handshake: Contributing

Please see [CONTRIBUTING.org](CONTRIBUTING.org) for guidelines on how to contribute to this project.

## :book: References

- [Algorithm Design with Haskell](https://www.cs.ox.ac.uk/publications/books/adwh/) - The original book this adaptation is based on

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/) - Official Lean 4 documentation

## :pushpin: License

This project is licensed under Apache License 2.0. See LICENSE.
