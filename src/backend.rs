pub struct Output {
    // TODO
}

pub trait Backend {
    fn execute(&mut self) -> Output;
}

/// A backend that does nothing. When executing a code object, it simply returns
/// an empty output.
pub struct NullBackend {}

impl NullBackend {
    pub fn new() -> NullBackend {
        NullBackend {}
    }
}

impl Backend for NullBackend {
    fn execute(&mut self) -> Output {
        Output {}
    }
}
