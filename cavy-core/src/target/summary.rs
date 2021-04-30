#![cfg(feature = "summary")]
//! This module and target are feature-gated because they depend on serde. It
//! would be nice not to have to add a dependency to all builds just because
//! it's used in this one place.

use crate::circuit::{CGate, FreeState, Inst, QGate};
use crate::session::Statistics;
use serde_json::{json, Map};

use std::time::Duration;

use super::*;

macro_rules! zero {
    ($($name:ident)*) => { $(let mut $name = 0;)* }
}

#[derive(Debug)]
pub struct Summary {
    pub perf: bool,
}

impl Target for Summary {
    fn from(&self, circ: CircuitBuf, ctx: &Context) -> ObjectCode {
        let qbits = circ.qbit_size();
        let cbits = circ.cbit_size();

        zero! {
            xgates tgates hgates zgates cxgates swapgates
            clean_frees dirty_frees
        };

        for inst in circ.into_iter() {
            match inst {
                Inst::CInit(_) => {}
                Inst::CFree(_, _) => {}
                Inst::QInit(_) => {}
                Inst::QFree(_, state) => match state {
                    FreeState::Clean => clean_frees += 1,
                    FreeState::Dirty => dirty_frees += 1,
                },
                Inst::QGate(g) => match g {
                    QGate::X(_) => xgates += 1,
                    QGate::T { .. } => tgates += 1,
                    QGate::H(_) => hgates += 1,
                    QGate::Z(_) => zgates += 1,
                    QGate::CX { .. } => cxgates += 1,
                    QGate::SWAP(_, _) => swapgates += 1,
                },
                Inst::CGate(_) => {}
                Inst::Meas(_, _) => {}
                Inst::Out(_) => {}
            }
        }

        let single_qubit_gates = xgates + tgates + hgates + zgates;
        let two_qubit_gates = cxgates + swapgates;
        let total_gates = single_qubit_gates + two_qubit_gates;

        let mut stats = json!({
            "bits": {
                "qbits": qbits,
                "cbits": cbits,
                "total": qbits + cbits,
            },
            "gates": {
                "X": xgates,
                "T": tgates,
                "H": hgates,
                "Z": zgates,
                "CX": cxgates,
                "SWAP": swapgates,
                "single-qubit": single_qubit_gates,
                "two-qubit": two_qubit_gates,
                "total": total_gates,
            },
            "frees": {
                "clean": clean_frees,
                "dirty": dirty_frees,
                "total": clean_frees + dirty_frees,
            }
        });

        if self.perf {
            let events = &ctx.stats.events;
            let mut times: Map<_, _> = events
                .windows(2)
                .map(|w| {
                    let label = w[1].label.to_string();
                    // `serde_json` doesn't support 128-bit numbers, so we have
                    // to downcast it here.
                    let delta = w[1].delta(&w[0]) as u64;
                    (label, json!(delta))
                })
                .collect();
            let total = events.last().unwrap().delta(&events[0]) as u64;
            times.insert("total".to_string(), json!(total));

            if let serde_json::Value::Object(ref mut map) = stats {
                map.insert("perf".to_string(), json!(times));
            } else {
                unreachable!();
            }
        }
        format!("{}", serde_json::to_string_pretty(&stats).unwrap())
    }
}
