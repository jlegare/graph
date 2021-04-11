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
#[derive(Debug)]
pub struct EdgeType<EdgePayloadType> {
    id: EdgeIdType,
    from: NodeIdType,
    to: NodeIdType,

    payload: EdgePayloadType,
    weight: f64,
}

impl<EdgePayloadType: Copy> EdgeType<EdgePayloadType> {
    pub(super) fn new(
        id: usize,
        from: NodeIdType,
        to: NodeIdType,
        payload: EdgePayloadType,
    ) -> Self {
        Self {
            id: EdgeIdType { id },
            from,
            to,
            payload,
            weight: -1.0,
        }
    }

    pub(super) fn id_of(&self) -> EdgeIdType {
        self.id
    }

    pub(super) fn payload_of(&self) -> EdgePayloadType {
        self.payload
    }

    pub(super) fn payload(&mut self, payload: EdgePayloadType) {
        self.payload = payload;
    }

    pub(super) fn vertices_of(&self) -> (NodeIdType, NodeIdType) {
        (self.from, self.to)
    }

    pub(super) fn weight(&mut self, weight: f64) {
        self.weight = weight;
    }

    pub(super) fn weight_of(&self) -> f64 {
        self.weight
    }
}

impl<EdgePayloadType: Eq> PartialEq for EdgeType<EdgePayloadType> {
    fn eq(&self, other: &Self) -> bool {
        self.from == other.from && self.to == other.to
    }
}

impl<EdgePayloadType: Eq> Eq for EdgeType<EdgePayloadType> {}

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
