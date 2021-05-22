//! These tests will check properties of compiled circuits

use cavy_core::circuit::{BaseGateQ, GateQ, Inst};

/// Test that a circuit implements the right unitary. This uses `qutip` to
/// simulate the circuit, but shouldn't depend on `inline_python` or even
/// `pycavy`; It will instead do the "most naive" thing possible.
macro_rules! test_unitary {
    ($($name:ident { $($src:tt)* } => [$($gates:expr),*])*) => {
        $(

            #[test]
            pub fn $name() -> io::Result<()> {
                // This is identical to the current stand-in `cavy` macro in
                // cavy/lib.rs. We can't necessarily use that macro, though,
                // because I want access to the config. Maybe it should *return*
                // the config? Not clear. Good enough for now.
                let mut stats = cavy_core::session::Statistics::new();
                let conf = cavy_core::session::Config::default();
                let mut ctx = cavy_core::context::Context::new(&conf, &mut stats);
                let id = ctx.srcs.insert_input(&stringify!($($src)*));
                let circ = cavy_core::compile::compile_circuit(id, &mut ctx).unwrap().unwrap();

                let max_qubit: u32 = circ.max_qbit.unwrap().into();
                let true_gates: String = circ.into_iter().map(|inst| circuit::inst_to_qutip(inst)).collect();

                let exp_gates = vec![$($gates.into()),*];
                let exp_gates: String = exp_gates.into_iter().map(|inst| circuit::inst_to_qutip(inst)).collect();

                let script = format!(
                    include_str!("circuit/circuit_test.py"),
                    purity = 1,
                    qubits = max_qubit + 1,
                    true_gates = true_gates,
                    exp_gates = exp_gates
                );

                let mut proc = std::process::Command::new("python")
                        .args(&["/dev/stdin"])
                        .stdin(std::process::Stdio::piped())
                        .stdout(std::process::Stdio::piped())
                        .spawn()?;

                let stdin = proc.stdin.as_mut().unwrap();
                stdin.write_all(script.as_bytes())?;
                drop(stdin);

                let output = proc.wait_with_output()?;
                assert!(output.status.success(), "{}", String::from_utf8(output.stderr).unwrap());

                Ok(())
            }
        )*
    };
}

pub fn inst_to_qutip(inst: Inst) -> String {
    match inst {
        Inst::CInit(_) => "".to_owned(),
        Inst::CFree(_, _) => "".to_owned(),
        Inst::QInit(_u) => "".to_owned(),
        Inst::QFree(_u, _) => "".to_owned(),
        Inst::QGate(g) => gate_to_qutip(g),
        Inst::CGate(_g) => "".to_owned(),
        Inst::Meas(_u, _) => "".to_owned(),
        Inst::Out(_) => "".to_owned(),
    }
}

pub fn gate_to_qutip(g: GateQ) -> String {
    use BaseGateQ::*;
    if g.ctrls.len() > 0 {
        todo!();
    }

    match g.base {
        X(u) => format!("qc.add_gate(\"X\", targets={})", u),
        H(u) => format!("qc.add_gate(\"H\", targets={})", u),
        Z(u) => format!("qc.add_gate(\"Z\", targets={})", u),
        T(u) => format!("qc.add_gate(\"T\", targets={})", u),
        TDag(_u) => todo!(),
        Cnot { ctrl, tgt } => format!("qc.add_gate(\"CNOT\", controls={}, targets={})", ctrl, tgt),
        Swap(fst, snd) => format!("qc.add_gate(\"SWAP\", targets=[{}, {}])", fst, snd),
    }
}
