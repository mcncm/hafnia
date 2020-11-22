/// In this module we outline the Backend api. This is pretty unstable for the
/// time being, so don’t rely on it.

/// There is a version 3 of QASM, but we’re only going to use 2.0 for now, since
/// this is what Cirq supports.
pub const QASM_VERSION: &'static str = "2.0";

pub trait Backend {
    type CodeObject;
}

pub trait BackendSerializable<T: Backend> {
    fn to_backend(&self) -> T::CodeObject;
}

///////////////////////
// Concrete Backends //
///////////////////////

pub struct NullBackend {}
impl Backend for NullBackend {
    type CodeObject = ();
}

impl NullBackend {
    pub fn new() -> Self {
        Self {}
    }
}

pub struct Qasm {}
impl Backend for Qasm {
    type CodeObject = String;
}
