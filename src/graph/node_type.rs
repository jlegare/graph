use std::fmt;
use std::vec::Vec;

use crate::graph::edge_type::EdgeIdType;

/* ------------------------------------------------------------------------
 * NODE ID TYPE
 */
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NodeIdType {
    id: usize,
}

impl NodeIdType {
    pub(crate) fn new(id: usize) -> Self {
        Self { id }
    }
}

/* ------------------------------------------------------------------------
 * NODE TYPE
 */
#[derive(Debug)]
pub struct NodeType<'a, NodePayloadType> {
    id: NodeIdType,
    incoming: Vec<EdgeIdType>,
    outgoing: Vec<EdgeIdType>,
    payload: &'a NodePayloadType,
}

impl<'a, NodePayloadType> NodeType<'a, NodePayloadType> {
    pub(crate) fn new(id: usize, payload: &'a NodePayloadType) -> Self {
        Self {
            id: NodeIdType::new(id),
            incoming: vec![],
            outgoing: vec![],
            payload,
        }
    }

    pub(crate) fn id_of(&self) -> NodeIdType {
        self.id
    }

    pub(crate) fn add_incoming(&mut self, edge_id: EdgeIdType) {
        if self.incoming.iter().find(|&id| *id == edge_id) == None {
            self.incoming.push(edge_id)
        }
    }

    pub(crate) fn add_outgoing(&mut self, edge_id: EdgeIdType) {
        if self.outgoing.iter().find(|&id| *id == edge_id) == None {
            self.outgoing.push(edge_id)
        }
    }

    pub(crate) fn outgoing_of(&self) -> Vec<&EdgeIdType> {
        self.outgoing.iter().collect()
    }

    pub(crate) fn payload(&mut self, payload: &'a NodePayloadType) {
        self.payload = payload
    }

    pub(crate) fn payload_of(&self) -> &'a NodePayloadType {
        self.payload
    }
}

/* ------------------------------------------------------------------------
 * NODE STATE
 */
#[derive(Debug, PartialEq)]
pub enum NodeState {
    Undiscovered,
    Discovered,
    Finished,
}

impl fmt::Display for NodeState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            NodeState::Undiscovered => write!(f, "white"),
            NodeState::Discovered => write!(f, "gray"),
            NodeState::Finished => write!(f, "black"),
        }
    }
}

/* ------------------------------------------------------------------------
 * UNIT TESTS
 */
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_type_001() {
        let correct_id = 5;
        let incorrect_id = 7;
        let node = NodeType::<()>::new(correct_id, &());

        assert_eq!(node.id, NodeIdType { id: correct_id });
        assert_ne!(node.id, NodeIdType { id: incorrect_id });
    }

    #[test]
    fn node_type_002() {
        let id = 5;
        let correct_payload = "CORRECT";
        let incorrect_payload = "INCORRECT";
        let node = NodeType::<&str>::new(id, &correct_payload);

        assert_eq!(node.payload_of(), &correct_payload);
        assert_ne!(node.payload_of(), &incorrect_payload);
    }

    #[test]
    fn node_type_003() {
        let id = 5;
        let correct_payload = "CORRECT";
        let incorrect_payload = "INCORRECT";
        let mut node = NodeType::<&str>::new(id, &incorrect_payload);

        node.payload(&correct_payload);

        assert_eq!(node.payload_of(), &correct_payload);
        assert_ne!(node.payload_of(), &incorrect_payload);
    }
}
