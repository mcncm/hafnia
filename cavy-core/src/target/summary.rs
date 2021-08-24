#![cfg(feature = "summary")]
//! This module and target are feature-gated because they depend on serde. It
//! would be nice not to have to add a dependency to all builds just because
//! it's used in this one place.

use crate::circuit::*;
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

        zero! [
            sqgates
                xgates tgates sgates hgates zgates arbphase_gates
            mqgates
                swapgates cxgates czgates cswapgates

            clean_frees dirty_frees
        ];

        for inst in circ.into_iter() {
            match inst {
                Inst::CInit(_) => {}
                Inst::CFree(_, _) => {}
                Inst::QInit(_) => {}
                Inst::QFree(_, state) => match state {
                    FreeState::Clean => clean_frees += 1,
                    FreeState::Dirty => dirty_frees += 1,
                },
                Inst::QGate(g) => {
                    use BaseGateQ::*;
                    if g.ctrls.len() > 0 || g.is_swap() || g.is_cx() {
                        mqgates += 1;

                        if g.is_cx() {
                            cxgates += 1;
                        } else if g.is_cz() {
                            czgates += 1;
                        } else if g.is_cswap() {
                            cswapgates += 1;
                        } else if g.is_swap() {
                            swapgates += 1;
                        }

                        continue;
                    }

                    sqgates += 1;
                    match g.base {
                        X(_) => xgates += 1,
                        H(_) => hgates += 1,
                        Z(_) => zgates += 1,
                        T(_) => tgates += 1,
                        TDag(_) => tgates += 1,
                        S(_) => sgates += 1,
                        SDag(_) => sgates += 1,
                        Phase(_, _) => arbphase_gates += 1,
                        // multiqubit base gates covered by the multiqubit gate
                        // checks above
                        Swap(_, _) => unreachable!(),
                        Cnot { .. } => unreachable!(),
                    }
                }
                Inst::CGate(_) => {}
                Inst::Meas(_, _) => {}
                Inst::Io(_) => {}
            }
        }

        let mut stats = json!({
            "bits": {
                "qbits": qbits,
                "cbits": cbits,
                "total": qbits + cbits,
            },
            "gates": {
                "sqgates": {
                    "x": xgates,
                    "t": tgates,
                    "s": sgates,
                    "h": hgates,
                    "z": zgates,
                    "arb_phase": arbphase_gates,
                    "total": sqgates,
                },
                "mqgates": {
                    "cx": cxgates,
                    "cz": czgates,
                    "swap": swapgates,
                    "cswap": cswapgates,
                    "total": mqgates
                },
                "total": sqgates + mqgates,
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
