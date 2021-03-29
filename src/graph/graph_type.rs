use std::collections::HashMap;

use crate::graph::edge_type::{EdgeIdType, EdgeType};
use crate::graph::node_type::{NodeIdType, NodeState, NodeType};

/* ------------------------------------------------------------------------
 * GRAPH TYPE
 */
#[derive(Debug)]
pub struct GraphType<EdgePayloadType, NodePayloadType>
where
    EdgePayloadType: Clone + Copy + PartialEq,
    NodePayloadType: Clone + Copy + PartialEq,
{
    name: String,
    edges: HashMap<EdgeIdType, EdgeType<EdgePayloadType>>,
    nodes: HashMap<NodeIdType, NodeType<NodePayloadType>>,
}

impl<EdgePayloadType, NodePayloadType> GraphType<EdgePayloadType, NodePayloadType>
where
    EdgePayloadType: Clone + Copy + PartialEq,
    NodePayloadType: Clone + Copy + PartialEq,
{
    pub fn new(name: &str) -> Self {
        GraphType {
            name: name.to_string(),
            edges: HashMap::new(),
            nodes: HashMap::new(),
        }
    }

    pub fn add_edge(
        &mut self,
        from: NodeIdType,
        to: NodeIdType,
        payload: EdgePayloadType,
    ) -> Result<EdgeIdType, String> {
        if !self.nodes.contains_key(&from) {
            Err(format!("The node {:?} does not exist.", from))
        } else if !self.nodes.contains_key(&to) {
            Err(format!("The node {:?} does not exist.", to))
        } else {
            let edge = EdgeType::new(self.edges.len() + 1, from, to, payload); // The "+ 1" is to make IDs start at 1.
            let id = edge.id_of();
            self.add_incoming(to, id);
            self.add_outgoing(from, id);
            self.edges.insert(id, edge);
            Ok(id)
        }
    }

    pub fn add_edge_by_payload(
        &mut self,
        from: NodePayloadType,
        to: NodePayloadType,
        payload: EdgePayloadType,
    ) -> Result<EdgeIdType, String> {
        self.add_edge(self.locate_node(from)?, self.locate_node(to)?, payload)
    }

    pub fn add_node(&mut self, payload: NodePayloadType) -> Result<NodeIdType, String> {
        let node = NodeType::new(self.nodes.len() + 1, payload); // The "+ 1" is to make IDs start at 1.
        let id = node.id_of();
        self.nodes.insert(id, node);
        Ok(id)
    }

    pub fn add_nodes(&mut self, payloads: &[NodePayloadType]) -> Result<Vec<NodeIdType>, String> {
        payloads
            .iter()
            .map(|&payload| self.add_node(payload))
            .collect()
    }

    fn add_incoming(&mut self, to: NodeIdType, edge: EdgeIdType) {
        // It was the caller's responsibility to check that to is present in self.nodes. So we can go ahead and unwrap()
        // without further ado.
        self.nodes.get_mut(&to).unwrap().add_incoming(edge)
    }

    fn add_outgoing(&mut self, from: NodeIdType, edge: EdgeIdType) {
        // It was the caller's responsibility to check that to is present in self.nodes. So we can go ahead and unwrap()
        // without further ado.
        self.nodes.get_mut(&from).unwrap().add_outgoing(edge)
    }

    fn locate_node(&self, payload: NodePayloadType) -> Result<NodeIdType, String> {
        match self
            .nodes
            .values()
            .filter(|node| node.payload_of() == payload)
            .next()
        {
            Some(node) => Ok(node.id_of()),
            None => Err("The node could not be located by payload.".to_string()), // This should really refer to the payload.
        }
    }

    pub fn depth_first(
        &self,
        source_node_id: NodeIdType,
    ) -> Result<(Vec<NodeIdType>, HashMap<NodeIdType, NodeState>), String> {
        self.depth_first_for_each(source_node_id, |_, _| {})
    }

    pub fn depth_first_for_each<CallbackType>(
        &self,
        source_node_id: NodeIdType,
        mut callback: CallbackType,
    ) -> Result<(Vec<NodeIdType>, HashMap<NodeIdType, NodeState>), String>
    where
        CallbackType:
            FnMut(Option<&EdgeIdType>, &NodeIdType) -> (),
    {
        let mut lexicographic: Vec<(Option<EdgeIdType>, NodeIdType)> = vec![];
        let mut node_states: HashMap<NodeIdType, NodeState> = self
            .nodes
            .keys()
            .map(|node_id| (*node_id, NodeState::Undiscovered))
            .collect();

        // Let's be careful with the entry point node ID we were given ... we'll ensure it actually belongs to our graph
        // before continuing.
        if let None = self.nodes.get(&source_node_id) {
            return Err(format!("Unable to find node {:?}.", source_node_id));
        };

        let targets_of = |node| {
            self.nodes[&node]
                .outgoing_of()
                .iter()
                .map(|edge| TargetItemType { via: Some(*edge), target: self.edges[edge].vertices_of().1 })
                .collect()
        };

        // But from now on, we can play fast and loose, because the only way to construct a graph is through the API we
        // provided, we guarantees consistency.
        let stack_item = StackItemType {
            origin: None,
            targets: vec![TargetItemType { via: None, target: source_node_id, }],
        };
        let mut stack: Vec<StackItemType> = vec![stack_item];
        let mut sorted: Vec<NodeIdType> = vec![];

        while !stack.is_empty() {
            let stack_item = stack.last_mut().unwrap();
            let targets = &mut stack_item.targets;

            if !targets.is_empty() {
                let target_item = targets.remove(0);
                let to = target_item.target;

                if *(node_states.get(&to).unwrap()) == NodeState::Discovered {
                    return Err(format!("Detected a cycle at node {:?}!", to));
                } else if *(node_states.get(&to).unwrap()) == NodeState::Undiscovered {
                    *(node_states.get_mut(&to).unwrap()) = NodeState::Discovered;
                    lexicographic.push((target_item.via.and_then(|edge_id| Some(*edge_id)), to));
                    stack.push(StackItemType {
                        origin: Some(to),
                        targets: targets_of(to),
                    });
                }
            } else {
                if let Some(node) = stack.pop().unwrap().origin {
                    node_states.insert(node, NodeState::Finished);
                    sorted.push(node);
                }
            }
        }

        lexicographic.iter().for_each(|(edge_id, node_id)| {
            callback(edge_id.as_ref(), node_id);
        });

        Ok((sorted, node_states))
    }

    fn shortest_path(
        &mut self,
        sorted: &Vec<NodeIdType>,
        source_node_id: &NodeIdType,
        target_node_id: &NodeIdType,
    ) -> Result<(f64, Vec<Option<EdgeIdType>>, Vec<NodeIdType>), String> {
        //
        // WIP: ADD CYCLE DETECTION!
        //
        type ChildrensType = HashMap<NodeIdType, HashMap<NodeIdType, EdgeIdType>>;
        type CostsType = HashMap<NodeIdType, f64>;
        type EdgesType = HashMap<NodeIdType, Option<EdgeIdType>>;
        type PredecessorsType = HashMap<NodeIdType, Option<NodeIdType>>;

        let mut childrens = ChildrensType::new();
        let mut costs = CostsType::new();
        let mut edges = EdgesType::new();
        let mut predecessors = PredecessorsType::new();

        let initialize = |childrens: &mut ChildrensType,
                          costs: &mut CostsType,
                          edges: &mut EdgesType,
                          predecessors: &mut PredecessorsType| {
            self.nodes.keys().for_each(|&node_id| {
                costs.insert(node_id, f64::INFINITY);
                edges.insert(node_id, None);
                predecessors.insert(node_id, None);

                childrens.insert(node_id, HashMap::new());
                let children = childrens.get_mut(&node_id).unwrap();
                self.nodes[&node_id].outgoing_of().iter().for_each(|&edge| {
                    let (_, to) = &self.edges[&edge].vertices_of();
                    children.insert(*to, *edge);
                });
            });
            *costs.get_mut(source_node_id).unwrap() = 0.0;
        };

        let cost_edges = |childrens: &mut ChildrensType,
                          costs: &mut CostsType,
                          edges: &mut EdgesType,
                          predecessors: &mut PredecessorsType| {
            let mut relax = |from: &NodeIdType, to: &NodeIdType| {
                let children = childrens.get(from).unwrap();

                let edge = children.get(to).unwrap();
                if costs[to] > costs[from] + self.edges[edge].weight_of() {
                    *costs.get_mut(to).unwrap() = costs[from] + self.edges[edge].weight_of();
                    *predecessors.get_mut(to).unwrap() = Some(*from);
                    *edges.get_mut(to).unwrap() = Some(*edge);
                }
            };

            sorted.iter().rev().for_each(|from| {
                self.nodes[from].outgoing_of().iter().for_each(|edge| {
                    let (_, to) = &self.edges[edge].vertices_of();
                    relax(from, to);
                });
            });
        };

        initialize(&mut childrens, &mut costs, &mut edges, &mut predecessors);
        cost_edges(&mut childrens, &mut costs, &mut edges, &mut predecessors);

        let mut path: Vec<NodeIdType> = vec![];
        let mut current_node = Some(target_node_id);

        while let Some(node) = current_node {
            path.push(*node);
            current_node = predecessors[node].as_ref();
        }

        Ok((
            costs[target_node_id],
            path.iter().map(|i| edges[i]).rev().collect(),
            path.iter().map(|i| *i).rev().collect(),
        ))
    }
}

/* ------------------------------------------------------------------------
 * STACK ITEM TYPE ... This is a helper struct used in dfs(), to (hopefully) clarify the code.
 */
#[derive(Debug)]
struct StackItemType<'a> {
    origin: Option<NodeIdType>,
    targets: Vec<TargetItemType<'a>>,
}

/* ------------------------------------------------------------------------
 * TARGET ITEM TYPE ... This is a helper struct used in dfs(), to (hopefully) clarify the code.
 */
#[derive(Debug)]
struct TargetItemType<'a> {
    via: Option<&'a EdgeIdType>,
    target: NodeIdType,
}

/* ------------------------------------------------------------------------
 * UNIT TESTS
 */
#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::node_type::NodeState::Finished;

    #[test]
    fn graph_type_001() {
        let correct_name = "CORRECT";
        let incorrect_name = "INCORRECT";
        let graph = GraphType::<(), ()>::new(correct_name);

        assert_eq!(graph.name, correct_name);
        assert_ne!(graph.name, incorrect_name);
    }

    #[test]
    fn graph_type_002() {
        let name = "GRAPH";
        let mut graph: GraphType<(), &str> = GraphType::new(name);
        let payloads = vec!["FIRST", "SECOND", "THIRD"];
        let node_ids: Vec<NodeIdType> = payloads
            .iter()
            .map(|payload| graph.add_node(payload).unwrap())
            .collect();

        assert_eq!(graph.nodes.len(), payloads.len());
        for node_id in &node_ids {
            assert!(graph.nodes.contains_key(node_id));
        }
    }

    #[test]
    fn graph_type_003() {
        let name = "GRAPH";
        let mut graph: GraphType<(), &str> = GraphType::new(name);
        let payloads = vec!["FIRST", "SECOND", "THIRD"];
        let node_ids = match graph.add_nodes(&payloads) {
            Ok(node_ids) => node_ids,
            Err(e) => std::panic::panic_any(e),
        };

        assert_eq!(graph.nodes.len(), payloads.len());
        for node_id in &node_ids {
            assert!(graph.nodes.contains_key(node_id));
        }
    }

    #[test]
    fn graph_type_004() {
        let name = "GRAPH";
        let mut graph: GraphType<(NodeIdType, NodeIdType), &str> = GraphType::new(name);
        let payloads = vec!["FIRST", "SECOND", "THIRD", "FOURTH", "FIFTH"];
        let node_ids = match graph.add_nodes(&payloads) {
            Ok(node_ids) => node_ids,
            Err(e) => std::panic::panic_any(e),
        };

        let mut edge_ids = vec![];
        node_ids[1..].iter().fold(node_ids[0], |from, &to| {
            match graph.add_edge(from, to, (from, to)) {
                Ok(edge_id) => edge_ids.push(edge_id),
                Err(e) => std::panic::panic_any(e),
            };
            to
        });

        assert_eq!(graph.edges.len(), edge_ids.len());
        for (i, edge_id) in edge_ids.iter().enumerate() {
            assert!(graph.edges.contains_key(edge_id));

            let (from, to) = graph.edges[edge_id].vertices_of();
            assert_eq!(node_ids[i], from);
            assert_eq!(node_ids[i + 1], to);
        }
    }

    #[test]
    fn graph_type_005() {
        let name = "GRAPH";
        let mut graph: GraphType<(NodeIdType, NodeIdType), &str> = GraphType::new(name);
        let payloads = vec!["FIRST", "SECOND", "THIRD", "FOURTH", "FIFTH"];
        let node_ids = match graph.add_nodes(&payloads) {
            Ok(node_ids) => node_ids,
            Err(e) => std::panic::panic_any(e),
        };

        let mut edge_ids = vec![];
        node_ids[1..].iter().fold(node_ids[0], |from, &to| {
            match graph.add_edge(from, to, (from, to)) {
                Ok(edge_id) => edge_ids.push(edge_id),
                Err(e) => std::panic::panic_any(e),
            };
            to
        });

        match graph.depth_first(node_ids[0]) {
            Ok((sorted, _)) => {
                assert_eq!(sorted.len(), node_ids.len());
                node_ids
                    .iter()
                    .rev()
                    .zip(sorted.iter())
                    .for_each(|(left, right)| assert_eq!(left, right));
            }
            Err(e) => std::panic::panic_any(e),
        };
    }

    #[test]
    fn graph_type_dfs_callback_01() {
        let name = "CALLBACK";
        let mut graph: GraphType<(), u32> = GraphType::new(name);
        let payloads = vec![1, 2, 3, 4, 5, 6, 7];
        let node_ids = graph.add_nodes(&payloads).unwrap();

        let edges_by_payload = [(1, 2), (1, 3), (2, 4), (2, 5), (3, 6), (3, 7)];
        let _edges: Vec<EdgeIdType> = edges_by_payload
            .iter()
            .map(|(from, to)| graph.add_edge_by_payload(*from, *to, ()).unwrap())
            .collect();

        let expected = [1, 2, 4, 5, 3, 6, 7];
        let mut result = Vec::<u32>::new();

        graph
            .depth_first_for_each(node_ids[0], |_, node_id| {
                let node = &graph.nodes[node_id];
                result.push(node.payload_of() * 2);
            })
            .unwrap();

        expected
            .iter()
            .zip(result)
            .for_each(|(left, right)| assert_eq!(*left * 2, right));
    }

    #[test]
    fn graph_type_dfs_tree() {
        let name = "TREE";
        let mut graph: GraphType<(), u64> = GraphType::new(name);
        let payloads = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let node_ids = graph.add_nodes(&payloads).unwrap();

        let edges_by_payload = [
            (1, 2),
            (1, 5),
            (1, 9),
            (2, 3),
            (5, 6),
            (5, 8),
            (9, 10),
            (3, 4),
            (6, 7),
        ];
        let _edges: Vec<EdgeIdType> = edges_by_payload
            .iter()
            .map(|(from, to)| graph.add_edge_by_payload(*from, *to, ()).unwrap())
            .collect();

        let lexicographical: Vec<NodeIdType> = payloads
            .iter()
            .map(|&id| NodeIdType::new(id as usize))
            .collect();
        let mut visited = vec![];

        let (_, states) = graph
            .depth_first_for_each(node_ids[0], |_, node| {
                visited.push(*node);
            })
            .unwrap();

        assert_eq!(lexicographical, visited);

        node_ids
            .iter()
            .for_each(|node_id| assert_eq!(states[node_id], Finished));
    }

    #[test]
    fn graph_type_dfs_dag_01() {
        let name = "DAG";
        let mut graph: GraphType<(), i32> = GraphType::new(name);
        let payloads = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let node_ids = graph.add_nodes(&payloads).unwrap();

        graph.add_edge_by_payload(1, 2, ()).unwrap();
        graph.add_edge_by_payload(1, 5, ()).unwrap();
        graph.add_edge_by_payload(1, 9, ()).unwrap();

        graph.add_edge_by_payload(2, 3, ()).unwrap();

        graph.add_edge_by_payload(5, 6, ()).unwrap();
        graph.add_edge_by_payload(5, 8, ()).unwrap();

        graph.add_edge_by_payload(9, 10, ()).unwrap();
        graph.add_edge_by_payload(3, 4, ()).unwrap();
        graph.add_edge_by_payload(6, 7, ()).unwrap();

        graph.add_edge_by_payload(4, 11, ()).unwrap();
        graph.add_edge_by_payload(7, 11, ()).unwrap();
        graph.add_edge_by_payload(8, 11, ()).unwrap();
        graph.add_edge_by_payload(10, 11, ()).unwrap();

        let lexicographical: Vec<NodeIdType> = [1, 2, 3, 4, 11, 5, 6, 7, 8, 9, 10]
            .iter()
            .map(|id| NodeIdType::new(*id as usize))
            .collect();
        let mut visited = vec![];

        let (_, states) = graph
            .depth_first_for_each(node_ids[0], |_, node| {
                visited.push(*node);
            })
            .unwrap();

        assert_eq!(lexicographical, visited);

        node_ids
            .iter()
            .for_each(|node_id| assert_eq!(states[node_id], Finished));
    }

    #[test]
    fn graph_type_dfs_dag_02() {
        let name = "DAG";
        let mut graph: GraphType<(), u32> = GraphType::new(name);

        let node_payloads = vec![2, 3, 4, 5, 6, 7, 1];
        let node_ids = graph.add_nodes(&node_payloads).unwrap();

        let edges_by_payload = [
            (2, 3),
            (2, 6),
            (3, 4),
            (6, 3),
            (7, 4),
            (1, 7),
            (7, 6),
            (6, 5),
        ];
        let _edges: Vec<EdgeIdType> = edges_by_payload
            .iter()
            .map(|(from, to)| graph.add_edge_by_payload(*from, *to, ()).unwrap())
            .collect();
        let expected = [2, 3, 4, 6, 5];
        let mut result = vec![];

        graph
            .depth_first_for_each(node_ids[0], |_, node| {
                result.push(graph.nodes[node].payload_of());
            })
            .unwrap();
        result
            .iter()
            .zip(expected.iter())
            .for_each(|(left, right)| assert_eq!(left, right));

        let expected = [1, 7, 4, 6, 3, 5];
        result.clear();
        graph
            .depth_first_for_each(node_ids[6], |_, node| {
                result.push(graph.nodes[node].payload_of());
            })
            .unwrap();
        result
            .iter()
            .zip(expected.iter())
            .for_each(|(left, right)| assert_eq!(left, right));
    }

    #[test]
    #[should_panic]
    fn graph_type_def_cycle_detection_01() {
        let name = "CYCLE DETECTION";
        let mut graph: GraphType<(), u32> = GraphType::new(name);

        let node_payloads = vec![2, 3, 6];
        let node_ids = graph.add_nodes(&node_payloads).unwrap();

        let edges_by_payload = vec![(2, 3), (3, 6), (6, 2)];
        let _edges: Vec<EdgeIdType> = edges_by_payload
            .iter()
            .map(|(from, to)| graph.add_edge_by_payload(*from, *to, ()).unwrap())
            .collect();

        let mut result = vec![];

        match graph.depth_first_for_each(node_ids[0], |_, node| {
            result.push(graph.nodes[node].payload_of());
        }) {
            Ok(_) => (),
            Err(e) => std::panic::panic_any(e),
        };
    }

    #[test]
    fn graph_type_shortest_path_02() {
        let name = "SHORTEST PATH";
        let mut graph: GraphType<u32, u32> = GraphType::new(name);
        let node_payloads = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let _node_ids = match graph.add_nodes(&node_payloads) {
            Ok(node_ids) => node_ids,
            Err(e) => std::panic::panic_any(e),
        };

        let edges_by_payload = vec![
            (1, 2, 1, 1),
            (1, 5, 2, 2),
            (1, 9, 5, 5),
            (2, 3, 6, 6),
            (5, 6, 3, 3),
            (5, 8, 4, 4),
            (9, 10, 7, 7),
            (3, 4, 1, 1),
            (6, 7, 2, 2),
            (4, 11, 1, 1),
            (7, 11, 3, 3),
            (8, 11, 5, 5),
            (10, 11, 3, 3),
        ];

        let _edge_ids: Vec<EdgeIdType> = edges_by_payload
            .iter()
            .map(|(from, to, payload, weight)| {
                let edge_id = graph.add_edge_by_payload(*from, *to, *payload).unwrap();
                graph
                    .edges
                    .get_mut(&edge_id)
                    .unwrap()
                    .weight(*weight as f64);

                edge_id
            })
            .collect();

        let source_node_id = graph.locate_node(1).unwrap();
        let target_node_id = graph.locate_node(11).unwrap();

        let expected_path: Vec<NodeIdType> = vec![1, 2, 3, 4, 11]
            .iter()
            .map(|payload| graph.locate_node(*payload).unwrap())
            .collect();
        let expected_cost = 9.0;

        let (sorted, _) = graph.depth_first(source_node_id).unwrap();
        let (result_cost, result_edges, result_path) = graph
            .shortest_path(&sorted, &source_node_id, &target_node_id)
            .unwrap();

        assert_eq!(expected_cost, result_cost);

        assert_eq!(expected_path, result_path);

        for (i, edge) in result_edges.iter().enumerate() {
            match edge {
                Some(edge) => {
                    let (from, to) = graph.edges[edge].vertices_of();

                    assert_eq!(expected_path[i - 1], from);
                    assert_eq!(expected_path[i], to);
                }
                None => (),
            };
        }
    }
}
