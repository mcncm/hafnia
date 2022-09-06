"""This little Python script provides some very primitive circuit simulation
utilities in pure numpy. We could instead write these tests in Rust, using a
suitable linear algebra library, but I'd rather use a lightweight scripting
language for the time being. It's perhaps a little bit regrettable to depend on
Python and Numpy, but it will do for now.

We could also rely on a fit-for-purpose dependency such as `qutip` or `qiskit`,
but there are a few reasons to avoid this: first, I don't know how much I can
trust the stability of these packages, however nice they appear; second, other
developers might find them difficult to use or install, but can be almost
assumed to have numpy already on their system; finally, I don't want to show
"favoritism" to one or another circuit simulation package.

Anyway, rest assured that this is not supposed to be fast or sophisticated.
Also, the first bit really should be a module separate from the script bit.
Despite the simplicity of this thing, I admit it's cribbed (though not verbatim)
from this (this nice blog post)[http://kattemolle.com/other/QCinPY.html] by
Joris Kattemölle. Go ahead, revoke my programming license.

"""

import numpy as np
from typing import Tuple, List


class Gate:

    I = np.array([
        [1, 0],
        [0, 1]
    ])

    X = np.array([
        [0, 1],
        [1, 0]
    ])

    Y = np.array([
        [0, -1j],
        [1j,  0]
    ])

    Z = np.array([
        [1,  0],
        [0, -1]
    ])

    H = np.array([
        [1,  1],
        [1, -1]
    ]) / np.sqrt(2)

    S = np.array([
        [1,  0],
        [0, 1j]
    ])

    Sdag = np.array([
        [1,   0],
        [0, -1j]
    ])

    T = np.array([
        [1,                      0],
        [0, np.exp(1j * np.pi / 4)]
    ])

    Tdag = np.array([
        [1,                       0],
        [0, np.exp(-1j * np.pi / 4)]
    ])

    CNOT = np.reshape(np.array([
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 0, 1],
        [0, 0, 1, 0]
    ]), (2, 2, 2, 2))

    SWAP = np.reshape(np.array([
        [1, 0, 0, 0],
        [0, 0, 1, 0],
        [0, 1, 0, 0],
        [0, 0, 0, 1]
    ]), (2, 2, 2, 2))

    CZ = np.reshape(np.array([
        [1, 0, 0,  0],
        [0, 1, 0,  0],
        [0, 0, 1,  0],
        [0, 0, 0, -1]
    ]), (2, 2, 2, 2))


class Circuit:

    def __init__(self, qubits: int):
        self.qubits = qubits
        self.gates: List[Tuple[np.ndarray, Tuple[int, ...], List[int]]] = []

    def append(self, gate: np.ndarray, targets: Tuple[int, ...], controls: List[int] = []):
        self.gates.append((gate, targets, controls))

    def run(self) -> np.ndarray:
        """Simulate the action of the circuit on an input |00...0> state.
        """
        state = np.zeros([2] * self.qubits)
        state[(0,) * self.qubits] = 1
        for (gate, targets, controls) in self.gates:
            shape_len = len(gate.shape)
            in_legs = tuple(range(shape_len // 2, shape_len))
            out_legs = tuple(range(shape_len // 2))
            state = np.tensordot(gate, state, (in_legs, targets))
            state = np.moveaxis(state, targets, out_legs)
        return state


# minimum acceptable purity of the output state
purity = {purity}
# number of qubits in the circuit
qubits = {qubits}

# no classical bits, for now
circ = Circuit(qubits)
{true_gates}
# The true output state
true_out = circ.run()

circ = Circuit(qubits)
{exp_gates}
# The test output state
test_out = circ.run()

# the two unitaries should be equal within tolerance
assert np.isclose(true_out, test_out).all()
