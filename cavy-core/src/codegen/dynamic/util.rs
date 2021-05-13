//! Some helper functions: these probably belong in the other files in this
//! module. The fact that I haven’t gotten them into one or another is a sign
//! that it’s not factored *quite* right.

/// Construct a teed-off closure from an ordinary one. Used mostly to clone a
/// stream of gates into a second collection, generally a destructor. This is in
/// the no-mans-land module because it’s still used by both `gates.rs` and
/// `compute.rs`.
pub fn tee<'s, IT, T, F, A>(f: F, sink: &'s mut Vec<T>) -> impl FnMut(A) -> IT + 's
where
    F: Fn(A) -> IT + 's,
    T: From<IT>,
    IT: Clone,
{
    move |a| {
        let val = f(a);
        sink.push(val.clone().into());
        val
    }
}
