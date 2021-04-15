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
    pub(crate) fn new(
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

    pub(crate) fn id_of(&self) -> EdgeIdType {
        self.id
    }

    pub(crate) fn payload_of(&self) -> EdgePayloadType {
        self.payload
    }

    pub(crate) fn payload(&mut self, payload: EdgePayloadType) {
        self.payload = payload;
    }

    pub(crate) fn vertices_of(&self) -> (NodeIdType, NodeIdType) {
        (self.from, self.to)
    }

    pub(crate) fn weight(&mut self, weight: f64) {
        self.weight = weight;
    }

    pub(crate) fn weight_of(&self) -> f64 {
        self.weight
    }
}

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

        assert_eq!(edge.payload_of(), correct_payload);
        assert_ne!(edge.payload_of(), incorrect_payload);
    }

    #[test]
    fn edge_type_003() {
        let from = NodeType::<&str>::new(5, "5");
        let to = NodeType::<&str>::new(7, "7");
        let id = 5;
        let correct_payload = "5 -> 7";
        let incorrect_payload = "7 -> 5";
        let mut edge = EdgeType::<&str>::new(id, from.id_of(), to.id_of(), incorrect_payload);

        edge.payload(correct_payload);

        assert_eq!(edge.payload_of(), correct_payload);
        assert_ne!(edge.payload_of(), incorrect_payload);
    }

    #[test]
    fn edge_type_004() {
        let from = NodeType::<&str>::new(5, "5");
        let to = NodeType::<&str>::new(7, "7");
        let id = 5;
        let correct_weight = 1.0;
        let incorrect_weight = 7.0;
        let mut edge = EdgeType::<&str>::new(id, from.id_of(), to.id_of(), "5 -> 7");

        edge.weight(correct_weight);

        assert!((edge.weight_of() - correct_weight).abs() < f64::EPSILON);
        assert!((edge.weight_of() - incorrect_weight).abs() > f64::EPSILON);
    }
}
