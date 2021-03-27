use crate::graph::node_type::NodeIdType;

/* ------------------------------------------------------------------------
 * EDGE ID TYPE
 */
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EdgeIdType {
    id: usize,
}

/* ------------------------------------------------------------------------
 * EDGE TYPE
 */
#[derive(Clone, Debug)]
pub struct EdgeType<EdgePayloadType: Clone + Copy>
where
    EdgePayloadType: Clone + Copy,
{
    id: EdgeIdType,
    from: NodeIdType,
    to: NodeIdType,

    payload: EdgePayloadType,
    weight: f64,
}

impl<EdgePayloadType> EdgeType<EdgePayloadType>
where
    EdgePayloadType: Clone + Copy,
{
    pub fn new(id: usize, from: NodeIdType, to: NodeIdType, payload: EdgePayloadType) -> Self {
        Self {
            id: EdgeIdType { id },
            from,
            to,
            payload,
            weight: -1.0,
        }
    }

    pub fn id_of(&self) -> EdgeIdType {
        self.id
    }

    pub fn payload_of(&self) -> EdgePayloadType {
        self.payload
    }

    pub fn payload(&mut self, payload: EdgePayloadType) {
        self.payload = payload;
    }

    pub fn vertices_of(&self) -> (NodeIdType, NodeIdType) {
        (self.from, self.to)
    }

    pub fn weight(&mut self, weight: f64) {
        self.weight = weight;
    }

    pub fn weight_of(&self) -> f64 {
        self.weight
    }
}

impl<EdgePayloadType> PartialEq for EdgeType<EdgePayloadType>
where
    EdgePayloadType: Clone + Copy + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.from == other.from && self.to == other.to && self.payload == other.payload
    }
}

impl<EdgePayloadType> Eq for EdgeType<EdgePayloadType> where EdgePayloadType: Clone + Copy + Eq {}

/* ------------------------------------------------------------------------
 * UNIT TESTS
 */
#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::node_type::NodeType;

    #[test]
    fn edge_type_001() {
        let from = NodeType::<&str>::new(5, "5");
        let to = NodeType::<&str>::new(7, "7");
        let correct_id = 5;
        let incorrect_id = 7;
        let payload = "5 -> 7";
        let edge = EdgeType::<&str>::new(correct_id, from.id_of(), to.id_of(), payload);

        assert_eq!(edge.id, EdgeIdType { id: correct_id });
        assert_ne!(edge.id, EdgeIdType { id: incorrect_id });
    }

    #[test]
    fn edge_type_002() {
        let from = NodeType::<&str>::new(5, "5");
        let to = NodeType::<&str>::new(7, "7");
        let id = 5;
        let correct_payload = "5 -> 7";
        let incorrect_payload = "7 -> 5";
        let edge = EdgeType::<&str>::new(id, from.id_of(), to.id_of(), correct_payload);

        assert_eq!(edge.payload, correct_payload);
        assert_ne!(edge.payload, incorrect_payload);
    }
}
