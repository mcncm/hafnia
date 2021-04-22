
<div align="center">
<img src="assets/cavies.svg" width=400 alt="Cavy logo: a capybara with pups."></img>
</div>

# Overview

[![Build Status](https://travis-ci.com/mcncm/cavy-lang.svg?token=wTZePJvDpqqWnfcvqYkS&branch=main)](https://travis-ci.com/mcncm/cavy-lang)

Cavy is a little imperative programming language for quantum computers.

For everyday programmers, it's designed to be accessible without cheating you
out of correctness. For working scientists, it's meant to give you more powerful
tools of abstraction than you're likely used to, and aspires to run on any
platform you might need.

You'll feel right at home here if you're familiar with Rust[2], but Cavy is a much
simpler language. The compiler generates code in multiple executable and
representational low-level circuit languages, including OpenQASM and Quantikz,
the LaTeX quantum circuits package. You can run it as a standalone compiler, a
REPL, or a domain-specific language within Rust or your favorite scripting
language. It even has an [Emacs mode](https://github.com/mcncm/cavy-mode)!

This is not the only quantum programming language out there. Both academic and
corporate researchers have written their own, some of which I've drawn
inspiration from. For the most part, I find the existing options harder to use.
Some are not at all abstracted from the quantum circuit model. Some are closely
tied to one platform. Many are either embedded in some difficult
metalanguage<sup>1</sup>, or are better understood as bare-bones
circuit-building libraries. They're all perfectly nice, though--I just wanted
one with Cavy's features! I hope you enjoy it, too.

**All the examples below are written as though the implementation were complete,
which it is not. Only some of these things actually work, and they’re not
documented yet.**

[1] Cavy can also be used in this way, but need not be!

[2] Its syntax and semantics are *strongly* inspired by rust. As a result,
you'll find that while its parser and backend are *de novo*, many of the IR data
structures are very similar to those of `rustc`. This is no accident: since
there's already a language out there that does these things, we might as well
learn from the good decisions they've made! A consequence of this heritage is
that reading this repository (especially its `ast.rs` and `mir.rs`) isn't a bad
way to get the gist of how `rustc` works.

# Examples
Because Cavy is a small language, we can get the gist of it by looking at
some simple examples. These are also meant to teach the major points of
departure of quantum mechanics from the classical intuition of most programmers.

## Quantum random number generation
One of the main applications of quantum technologies used today is the
production of entropy with the strongest possible guarantees of _true physical
randomness_. Below is some sample Cavy code implementing a simple one-byte QRNG.

```rust
let q: ?u8 = 0;  // Declare a "qubyte" unsigned int, deterministically initialized to 0.
q = split(q);    // Split the wavefunction into 256 branches of equal weight.
let c = !q;      // Consume the ?u8 and bind its measured value to a u8.
```

This should look reasonably familiar to those familiar with conventional
imperative programming languages--especially Rust. There are a few novel
features, though.

The first is the `?` annotation, which denotes the following type as _linear_.
Linear types (or their weaker _affine_ cousins) exist in a few other languages,
including Rust, Idris 2, and other experimental quantum programming languages
like QML and QWIRE. They represent values that cannot be _cloned_ or _deleted_.
They must be consumed in exactly one place. It turns out that, in a remarkable
terminological coincidence (or is it?), this is exactly the
[constraint](https://en.wikipedia.org/wiki/No-cloning_theorem) imposed on
quantum states by the
[linearity](https://en.wikipedia.org/wiki/Quantum_superposition) of quantum
mechanics. In Cavy, the _relevance_ (must-use) constraint is relaxed; as in
Rust, values are "dropped" when they go out of scope. However, we’re constrained
by an extra rule, that linear values _have no concrete value_ until they’re
unwrapped in a specific way. If this were not so, it would cause all kinds of
physical paradoxes, and we don't want to break the universe--we're just here to
program!

Next is the `split` builtin function, which splits the wavefunction of the
just-initialized qubyte into an equal superposition of quantum sates |0⟩ + |1⟩ +
... + |255⟩. This function compiles to an operation on each qubit of the `?u8`
that quantum information scientists call a [Hadamard
gate](https://en.wikipedia.org/wiki/Hadamard_transform#Quantum_computing_applications),
something like a "quantum-parallel coin flip."

Finally, we meet the `!` (read "of course" or "measurement") operator, which
"delinearizes" (unwraps) the `?u8` to a `u8`. _One_ of the 256 wavefunction
branches is chosen--at random, and according to the [Born
rule](https://en.wikipedia.org/wiki/Born_rule)--as its classical value. The use
of `!` for "of course" is standard in the PL literature on linear typing,
and I like its evocation of asserting a concrete classical value from an
"indeterminate" (`?`) quantum state<sup>2</sup>. 

## Quantum interference

Let's consider another example, and introduce another feature of quantum
mechanics. In particular, we'll see how the `split` function differs from a mere
coin flip.

```rust
let q: ?bool = false;  // Declare a qubit.
q = split(q);          // Branch the wavefunction.
q = split(q);          // Branch it... again?
let c = !q;
```

If acting on a qubit with `split` were like flipping a coin, this program's
output would be a random bit, since a coin flipped twice still has even odds of
landing heads or tails. But quantum randomness is not like classical randomness.
In fact, the output of this program is *always* `false`. When the second `split`
is called, both the |0⟩ and
|1⟩ branches split in turn,

```text
              |0⟩  <------------- After line 1, above
             /   \
            /     \
           /       \
          /         \
        |0⟩    +    |1⟩  <------- After line 2
        / \         / \
       /   \       /   \
     |0⟩ + |1⟩ + |0⟩ - |1⟩  <---- After line 3
```

but one of the sub-branches picks up a minus sign, annihilating the weight on
|1⟩ through _interference_. This isn't a design choice within Cavy; the [laws of quantum mechanics](https://en.wikipedia.org/wiki/Unitarity_(physics)) dictate this minus sign. Every call to `split` really _does_ split the wavefunction on the current branch, but the value-dependent sign causes some branches to wash out.

## Entanglement generation
We can create an entangled pair like this:

```rust
// Initialize two qubits to the state |0⟩|0⟩
let q1 = ?false;
let q2 = ?false;

q1 = split(q1); // Our little register is now in the state |0⟩|0⟩ + |1⟩|0⟩.
if q2 {         // On the branch where q0 is |1⟩...
    q2 = ~q2;   // Negate q2.
}               // Now we have a Bell pair, |0⟩|0⟩ + |1⟩|1⟩.

// Read out the register!
let c1 = !q1;
let c2 = !q2;
```

The state of the classical register will always be either `c1 = false, c2 = false` or `c1 = true, c2 = true`.

<!--
## Grover's algorithm

This is where we'll see our first genuine asymptotic quantum speedup (only a
quadratic one, but a speedup nonetheless!).

Suppose we have a subroutine

```cavy
mem <- qalloc(n);

```
-->

# Installation

## On your personal computer
You can build and install a Cavy binary with Cargo. Clone the repository, `cd`
to the Cavy directory, and run `$ cargo build --release && cargo install --path
.`. Make sure that `~/.cargo/bin` is in your `PATH` variable. It should build
and run on Rust stable, beta, and nightly, and on Linux, MacOS, and Windows. I
don’t anticipate any architecture-dependence, but am curious to know if it
builds and runs on aarch64. Cavy currently requires rustc >= 1.48.0.

## For your quantum computing infrastructure
Cavy is probably too unstable for most experimental research, but if you’re
interested in learning more, please email `cavy` dash `lang` dash `support` at
`mit` dot `edu`.

# Usage

You can invoke the cavy compiler binary as `cavy`. If given no command line
arguments, it spawns a REPL.

## Interfacing with scripting languages

### Python
You can call the Cavy compiler from Python through
[pycavy](https://github.com/mcncm/pycavy) wrapper, which provides utility
functions for compiling Cavy programs and loading them as
[https://github.com/quantumlib/Cirq](Cirq) and [https://qiskit.org/](Qiskit)
circuits.

### Others
If I hear of any interest from the community, I would be happy to put out
similar wrappers for Javascript, Ruby, Julia, and so on.

## As a Rust crate
The Cavy crate will (soon) export a convenience macro for compiling and
executing inline Cavy programs.

# Features

# Development

Cavy has an Emacs major mode,
[cavy-mode.el](https://github.com/mcncm/cavy-mode), which provides syntax
highlighting and object code display (in QASM or as a LaTeX circuit).

# Contributing
If you discover a bug, want to contribute to the compiler, or talk about its
design and goals, please open an issue and/or email `cavy` dash `lang` dash
`support` at `mit` dot `edu`. Pull requests are welcome!
