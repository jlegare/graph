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
    pub fn new(id: usize) -> Self {
        Self { id }
    }
}

/* ------------------------------------------------------------------------
 * NODE TYPE
 */
#[derive(Clone, Debug)]
pub struct NodeType<NodePayloadType: Clone + Copy>
where
    NodePayloadType: Clone + Copy,
{
    id: NodeIdType,
    incoming: Vec<EdgeIdType>,
    outgoing: Vec<EdgeIdType>,
    payload: NodePayloadType,

    cost: f64,
}

impl<NodePayloadType> NodeType<NodePayloadType>
where
    NodePayloadType: Clone + Copy,
{
    pub fn new(id: usize, payload: NodePayloadType) -> Self {
        Self {
            id: NodeIdType { id },
            incoming: vec![],
            outgoing: vec![],
            payload,

            cost: f64::INFINITY,
        }
    }

    pub fn reset(&mut self) {
        self.cost = f64::INFINITY;
    }

    pub fn id_of(&self) -> NodeIdType {
        self.id
    }

    pub fn add_incoming(&mut self, edge_id: EdgeIdType) {
        match self.incoming.iter().find(|&id| *id == edge_id) {
            None => self.incoming.push(edge_id),
            _ => {}
        }
    }

    pub fn add_outgoing(&mut self, edge_id: EdgeIdType) {
        match self.outgoing.iter().find(|&id| *id == edge_id) {
            None => self.outgoing.push(edge_id),
            _ => {}
        }
    }

    pub fn cost(&mut self, cost: f64) {
        self.cost = cost;
    }

    pub fn outgoing_of(&self) -> Vec<&EdgeIdType> {
        self.outgoing.iter().collect()
    }

    pub fn payload(&mut self, payload: NodePayloadType) {
        self.payload = payload
    }

    pub fn payload_of(&self) -> NodePayloadType {
        self.payload
    }
}

impl<NodePayloadType> PartialEq for NodeType<NodePayloadType>
where
    NodePayloadType: Clone + Copy + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.payload == other.payload
    }
}

impl<NodePayloadType> Eq for NodeType<NodePayloadType> where NodePayloadType: Clone + Copy + Eq {}

/* ------------------------------------------------------------------------
 * NODE STATE
 */
#[derive(Clone, Copy, Debug, PartialEq)]
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
        let payload = ();
        let node = NodeType::<()>::new(correct_id, payload);

        assert_eq!(node.id, NodeIdType { id: correct_id });
        assert_ne!(node.id, NodeIdType { id: incorrect_id });
    }

    #[test]
    fn node_type_002() {
        let id = 5;
        let correct_payload = "CORRECT";
        let incorrect_payload = "INCORRECT";
        let node = NodeType::<&str>::new(id, correct_payload);

        assert_eq!(node.payload, correct_payload);
        assert_ne!(node.payload, incorrect_payload);
    }
}
