//! Error types and messages for parsing into the AST

use super::Node;

pub struct Error<'a> {
    pub kind: Kind<'a>,
    pub src: Option<Source<'a>>,
}

// A placeholder error kind until we need more
pub type Kind<'a> = &'a str;

pub enum Source<'a> {
    Node(Node<'a>),
    EOF,
}

impl<'a> From<Node<'a>> for Source<'a> {
    fn from(node: Node<'a>) -> Source<'a> {
        Source::Node(node)
    }
}
