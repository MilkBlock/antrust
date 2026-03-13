#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Source {
    E(usize),
    K,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Reference {
    pub src: Source,
    pub hole_idx: usize,
    pub offset: i32,
    pub values_count: i32,
}
