//! These tests will check properties of compiled circuits

use hafnia_core::circuit::{BaseGateQ, GateQ, Inst};

use std::io::{self, Write};

/// Test that a circuit implements the right unitary. This uses Numpy to
/// simulate the circuit, but shouldn't depend on `inline_python` or even
/// `pyhafnia`; It will instead do the "most naive" thing possible.
macro_rules! test_unitary {
    ($($name:ident { $($src:tt)* } => [$($gates:expr),*])*) => {
        $(

            #[test]
            pub fn $name() -> std::io::Result<()> {
                let src = stringify!($($src)*);
                let exp_gates = vec![$($gates.into()),*];
                circuit::test_unitary_inner(src, exp_gates)
            }
        )*
    };
}

pub fn test_unitary_inner(src: &'static str, exp_gates: Vec<Inst>) -> io::Result<()> {
    // This is identical to the current stand-in `hafnia` macro in
    // hafnia/lib.rs. We can't necessarily use that macro, though,
    // because I want access to the config. Maybe it should *return*
    // the config? Not clear. Good enough for now.
    let mut stats = hafnia_core::session::Statistics::new();
    let conf = hafnia_core::session::Config::default();
    let mut ctx = hafnia_core::context::Context::new(&conf, &mut stats);
    let id = ctx.srcs.insert_input(&src);
    let circ = hafnia_core::compile::compile_circuit(id, &mut ctx)
        .unwrap()
        .unwrap();

    let max_qubit: u32 = circ.max_qbit.unwrap().into();
    let true_gates: String = circ.into_iter().map(|inst| inst_to_circ(inst)).collect();

    let exp_gates: String = exp_gates
        .into_iter()
        .map(|inst| inst_to_circ(inst))
        .collect();

    let script = format!(
        include_str!("circuit_test.py"),
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
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8(output.stderr).unwrap()
    );

    Ok(())
}

pub fn inst_to_circ(inst: Inst) -> String {
    match inst {
        Inst::CInit(_) => "".to_owned(),
        Inst::CFree(_, _) => "".to_owned(),
        Inst::QInit(_u) => "".to_owned(),
        Inst::QFree(_u, _) => "".to_owned(),
        Inst::QGate(g) => gate_to_circ(g),
        Inst::CGate(_g) => "".to_owned(),
        Inst::Meas(_u, _) => "".to_owned(),
        Inst::Io(_) => "".to_owned(),
    }
}

pub fn gate_to_circ(g: GateQ) -> String {
    use BaseGateQ::*;
    if !g.ctrls.is_empty() {
        // FIXME hideous special casing
        if g.ctrls.len() == 1 {
            let ctrl = g.ctrls[0];
            return match g.base {
                X(u) if ctrl.1 => format!("circ.append(Gate.CNOT, ({}, {}))\n", ctrl.0, u),
                Z(u) if ctrl.1 => format!("circ.append(Gate.CZ, ({}, {}))\n", ctrl.0, u),
                _ => todo!(),
            };
        } else {
            todo!();
        }
    }

    match g.base {
        X(u) => format!("circ.append(Gate.X, ({},))\n", u),
        H(u) => format!("circ.append(Gate.Y, ({},))\n", u),
        Z(u) => format!("circ.append(Gate.Z, ({},))\n", u),
        T(u) => format!("circ.append(Gate.T, ({},))\n", u),
        TDag(_u) => todo!(),
        S(u) => format!("circ.append(Gate.S, ({},))\n", u),
        SDag(_u) => todo!(),
        Phase(_u, _phase) => todo!(),
        Cnot { ctrl, tgt } => format!("circ.append(Gate.CNOT, ({}, {}))\n", ctrl, tgt),
        Swap(fst, snd) => format!("circ.append(Gate.SWAP, ({}, {}))\n", fst, snd),
    }
}
