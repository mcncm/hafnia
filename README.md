
<div align="center">
<img src="assets/cavies.svg" width=400 alt="Cavy logo: a capybara with pups."></img>
</div>

# Overview

[![Build Status](https://travis-ci.com/mcncm/cavy-lang.svg?token=wTZePJvDpqqWnfcvqYkS&branch=main)](https://travis-ci.com/mcncm/cavy-lang)

Cavy is an imperative programming language for quantum computers. It's designed
to be accessible to everyday programmers, without cheating you out of
correctness. It uses a internal intermediate representation (IR) to generate
code in multiple low-level circuit languages, including OpenQASM and Quantikz.
You can run it on real hardware--or in a simulator--through an easy-to-use
Python wrapper. And it has a REPL, too!

This is not the only quantum programming language out there. Both academic and
corporate researchers have written their own. I'm just a student who did this
for fun, and make no claims to extreme originality in any of Cavy's
components--but I do think that the whole package is something pretty special.
For the most part, the existing options are a good deal harder to use for
beginners--sometimes not being at all abstracted from the quantum circuit
model--and either _(a)_ exist as DSLs embedded in some metalanguage (_e.g._ the
fantastic Quipper, which did a lot to inspire Cavy), or _(b)_ are actually
libraries. Many of them are perfectly nice, though. I just wanted one with
Cavy's features!

**All the examples below are written as though the implementation were complete,
which it is not. Only some of these things actually work, and they’re not
documented yet.**

# Examples
Cavy is a small language, so we can get the gist of it by looking at some simple
examples. These are also meant to teach the major points of departure of quantum
mechanics from the classical intuition of most programmers.

## Quantum random number generation
One of the main applications of quantum technologies used today is the
production of entropy with the strongest possible guarantees of _true physical
randomness_. Below is some sample Cavy code implementing a simple one-byte QRNG.

```cavy
let q: ?u8 = 0;  // Declare a "qubyte" unsigned int, deterministically initialized to 0.
q = split(q);    // Split the wavefunction into 256 branches of equal weight.
r = !q;          // Consume the ?u8 and bind its measured value to a u8.
print r;        // Write the random int to stdout.
```

This should look reasonably familiar to those familiar with conventional
imperative programming languages--especially Rust. There are a few novel
features, though.

The first is the `?` annotation, which denotes the following type as _linear_.
Linear types (or their weaker _affine_ cousins) exist in a few other languages,
including Rust, Haskell, and the perhaps-less-mainstream Idris 2. They represent
values that cannot be _cloned_ or _deleted_. In other words, they must be
consumed in exactly one place. It turns out that, in a remarkable terminological
coincidence (or is it?), this is exactly the
[constraint](https://en.wikipedia.org/wiki/No-cloning_theorem) imposed on
quantum states by the
[linearity](https://en.wikipedia.org/wiki/Quantum_superposition) of quantum
mechanics. In Cavy, the _relevance_ (must-be-used) constraint is relaxed; unused
linear variables are used "implicitly." However, Cavy imposes an additional
rule, which is that linear variables _have no concrete value_ that you can
interact with until the variable is unwrapped in one specific way. If this were
not so, it would cause all kinds of physical paradoxes, and we don't want to
break the universe--we're just here to program!

Next is the `split` builtin function, which splits the wavefunction of the
just-initialized qubyte into an equal superposition of quantum sates |0⟩ + |1⟩ +
... + |255⟩. This function compiles to an operation on each qubit of the `?u8`
that quantum information scientists call a [Hadamard
gate](https://en.wikipedia.org/wiki/Hadamard_transform#Quantum_computing_applications),
which is something like a "quantum-parallel coin flip." 

Finally, we meet the `!` (read "of course" or "measurement") operator, which
"delinearizes" the `?u8` to a `u8`. _One_ of the 256 wavefunction branches is
chosen--at random, and according to the [Born
rule](https://en.wikipedia.org/wiki/Born_rule)--as its classical value. The use
of `!` for "of course" is standard in the PL theory literature on linear typing,
and I like its evocation of asserting a concrete classical value from an
"indeterminate" (`?`) quantum state. However, we've had to pick some other
notation (namely, `~`) for our logical-not operator.

## Quantum interference

Let's consider a slightly more comicated example, which will introduce another
feature of quantum mechanics. In particular, we'll see how the `split` function
differs from a mere coin flip.

```cavy
let q: ?bool = false;  // Declare a qubit.
q = split(q);          // Branch the wavefunction.
q = split(q);          // Branch it... again?
print(!q);             // Write the "random" boolean to stdout.
```

If acting on a qubit with `split` were like flipping a coin, This program's
output trace would be a random bit, since a coin flipped twice still has equal
odds of landing heads or tails. But quantum randomness is not like classical
randomness. In fact, the output of this program is always `false`. When the
second `split` is called, both the |0⟩ and
|1⟩ branches split in turn:

              |0⟩  <------------- After line 1, above
             /   \
            /     \
           /       \
          /         \
        |0⟩    +    |1⟩  <------- After line 2
        / \         / \
       /   \       /   \
     |0⟩ + |1⟩ + |0⟩ - |1⟩  <---- After line 3

The [laws of quantum
mechanics](https://en.wikipedia.org/wiki/Unitarity_(physics)) dictate that there
must be a minus sign, causing _interference_ between branches of the
wavefunction, and annihilating the weight on |1⟩. Every call to `split` really
_does_ split the wavefunction on the current branch, but the value-dependent
signs cause some branches to wash out: this is quantum interference, the
fundamental property of from which all the other "weirdness" follows.

## Entanglement generation
We can create an entangled pair like this:

```cavy
// Initialize two qubuts to the state |0⟩|0⟩
let q1 = ?false;
let q2 = ?false;

q1 = split(q1); // Our little register is now in the state |0⟩|0⟩ + |1⟩|0⟩.
if q2 {         // On the branch where q0 is |1⟩...
    q2 = ~q2;   // Invert q1.
}               // Now we have a Bell pair, |0⟩|0⟩ + |1⟩|1⟩.

// Read out the register!
c1 = !q1; print c1;
c2 = !q2; print c2;
```

This program's trace will always be either `0\n0` `1\n1`.

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
don’t anticipate any architecture-dependence, but am curious to know if it builds
and runs on aarch64. Cavy currently requires rustc >= 1.48.0.

## For your quantum computing infrastructure
Please email `cavy` dash `lang` dash `support` at `mit` dot `edu`.

# Interfacing with scripting languages

## Python
You can call the Cavy compiler from Python through
[pycavy](https://github.com/mcncm/pycavy) wrapper, which provides utility
functions for loading compiling Cavy programs as Cirq and Qiskit circuits, LaTeX
diagrams, and so on.

## Julia
I’ll also put out a Julia wrapper--and sooner, if I hear of any interest!

# Development

Cavy has an Emacs major mode,
[cavy-mode.el](https://github.com/mcncm/cavy-mode), which provides syntax
highlighting and object code display (in QASM or as a LaTeX circuit).

# Contributing
If you discover a bug, want to contribute to the compiler, or talk about its
design and goals, please open an issue and/or email `cavy` dash `lang` dash
`support` at `mit` dot `edu`. Pull requests are welcome!
