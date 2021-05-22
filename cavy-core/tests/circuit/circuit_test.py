from qutip import basis, isequal, tensor
from qutip.qip.circuit import Gate, QubitCircuit

if __name__ == "__main__":
    # minimum acceptable purity of the output state
    purity = {purity}
    # number of qubits in the circuit
    qubits = {qubits}

    # no classical bits, for now
    qc = QubitCircuit(N=qubits, num_cbits=0)
    {true_gates}
    true_props = qc.propagators()
    if len(true_props) == 0:
        exit()
    true_unitary = true_props[0]
    for prop in true_props[1:]:
        true_unitary *= prop

    qc = QubitCircuit(N=qubits, num_cbits=0)
    {exp_gates}
    exp_props = qc.propagators()
    if len(exp_props) == 0:
        exit()
    exp_unitary = exp_props[0]
    for prop in exp_props[1:]:
        exp_unitary *= prop

    # the two unitaries should be equal within tolerance
    assert isequal(true_unitary, exp_unitary)
