#[macro_export]
macro_rules! alist {
    () => {
        $crate::AList::new()
    };
    ($($k:expr => $v:expr),+ $(,)?) => {
        $crate::AList::from_iter([$(($k, $v)),+])
    };
}
