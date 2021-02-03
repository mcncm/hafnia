use crate::arch::Arch;
use crate::cavy_errors::ErrorBuf;
use crate::circuit::Qubit;
use crate::values::Value;
use std::convert::TryInto;

pub trait Allocator<T> {
    fn alloc(&mut self, n: usize) -> Result<Vec<T>, ErrorBuf>;

    // This signature maybe ought to be `... -> Result<usize, Error>` or
    // something. We’ll see how it does for now.
    fn free(&mut self, addr: usize);
}

/// The default (and currently only) allocator used by the Interpreter. The
/// implementation does not try to be clever: allocations are only ever
/// performed after the greatest qubit yet allocated. This means that qubits are
/// never reused, which is a sound policy to begin with, especially as we know
/// nothing about the reinitialization capability of the target hardware.
///
/// # Examples
/// ```
/// # use cavy::values::Value;
/// # use cavy::alloc::QubitAllocator;
/// # use cavy::arch;
/// let arch = arch::Arch::default();
/// let mut allocator = QubitAllocator::new(arch);
/// let qb0 = allocator.alloc_q_bool().unwrap();
/// let qb1 = allocator.alloc_q_bool().unwrap();
/// assert_eq!(qb0, Value::Q_Bool(0));
/// assert_eq!(qb1, Value::Q_Bool(1));
/// ```
pub struct QubitAllocator {
    least_free: usize,
    arch: Arch,
}

impl Allocator<Qubit> for QubitAllocator {
    fn alloc(&mut self, n: usize) -> Result<Vec<Qubit>, ErrorBuf> {
        let end = self.least_free + n;
        if self.arch.qb_count < end.into() {
            // Should fail if we run out of qubits!
            todo!();
        }
        let qubits = (self.least_free..end).collect();
        self.least_free = end;
        Ok(qubits)
    }

    /// Yes, this is a no-op.
    fn free(&mut self, _addr: usize) {}
}

impl QubitAllocator {
    pub fn new(arch: Arch) -> Self {
        Self {
            least_free: 0,
            arch,
        }
    }

    pub fn q_bool(&mut self) -> Result<Vec<Qubit>, ErrorBuf> {
        Ok(self.alloc(1)?)
    }

    pub fn free_q_bool(&mut self, val: Value) {
        match val {
            Value::Q_Bool(index) => {
                self.free(index);
            }
            _ => {
                todo!();
            }
        }
    }

    pub fn q_u8(&mut self) -> Result<Vec<Qubit>, ErrorBuf> {
        Ok(self.alloc(8)?.try_into().unwrap())
    }

    pub fn alloc_q_u16(&mut self) -> Result<Vec<Qubit>, ErrorBuf> {
        Ok(self.alloc(16)?.try_into().unwrap())
    }

    pub fn alloc_q_u32(&mut self) -> Result<Vec<Qubit>, ErrorBuf> {
        Ok(self.alloc(32)?.try_into().unwrap())
    }
}
