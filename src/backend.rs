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
