use std::collections::vec_deque::VecDeque;
use std::collections::HashMap;

use crate::graph::edge_type::{EdgeIdType, EdgeType};
use crate::graph::node_type::{NodeIdType, NodeState, NodeType};

/* ------------------------------------------------------------------------
 * GRAPH TYPE
 */
#[derive(Debug)]
pub struct GraphType<'a, EdgePayloadType, NodePayloadType>
where
    EdgePayloadType: PartialEq,
    NodePayloadType: PartialEq,
{
    name: String,
    edges: HashMap<EdgeIdType, EdgeType<'a, EdgePayloadType>>,
    nodes: HashMap<NodeIdType, NodeType<'a, NodePayloadType>>,
}

impl<'a, EdgePayloadType, NodePayloadType> GraphType<'a, EdgePayloadType, NodePayloadType>
where
    EdgePayloadType: PartialEq,
    NodePayloadType: PartialEq,
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
        payload: &'a EdgePayloadType,
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

    pub fn add_node(&mut self, payload: &'a NodePayloadType) -> Result<NodeIdType, String> {
        let node = NodeType::new(self.nodes.len() + 1, payload); // The "+ 1" is to make IDs start at 1.
        let id = node.id_of();
        self.nodes.insert(id, node);
        Ok(id)
    }

    pub fn add_nodes(
        &mut self,
        payloads: &[&'a NodePayloadType],
    ) -> Result<Vec<NodeIdType>, String> {
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

    pub fn breadth_first<CallBackType>(
        &'a self,
        source_node_id: NodeIdType,
        finished: CallBackType,
    ) -> BreadthFirstIterator<'a, EdgePayloadType, NodePayloadType, CallBackType>
    where
        CallBackType: FnMut(&NodeType<NodePayloadType>),
    {
        BreadthFirstIterator::new(source_node_id, &self.edges, &self.nodes, finished)
    }

    pub fn depth_first<CallBackType>(
        &'a self,
        source_node_id: NodeIdType,
        finished: CallBackType,
    ) -> DepthFirstIterator<'a, EdgePayloadType, NodePayloadType, CallBackType>
    where
        CallBackType: FnMut(&NodeType<NodePayloadType>),
    {
        DepthFirstIterator::new(source_node_id, &self.edges, &self.nodes, finished)
    }

    pub fn shortest_path(
        &mut self,
        sorted: &[NodeIdType],
        source_node_id: &NodeIdType,
        target_node_id: &NodeIdType,
    ) -> Result<(f64, EdgeIdsType, NodeIdsType), String> {
        // This implementation assumes that the nodes have been topologically-sorted ... i.e., run through depth_first().
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
            path.into_iter().rev().collect(),
        ))
    }
}

/* ------------------------------------------------------------------------
 * BREADTH FIRST ITERATOR
 */
#[derive(Debug)]
pub struct BreadthFirstIterator<'a, EdgePayloadType, NodePayloadType, CallBackType>
where
    EdgePayloadType: PartialEq,
    NodePayloadType: PartialEq,
    CallBackType: FnMut(&NodeType<'a, NodePayloadType>),
{
    source_node_id: NodeIdType,
    edges: &'a HashMap<EdgeIdType, EdgeType<'a, EdgePayloadType>>,
    nodes: &'a HashMap<NodeIdType, NodeType<'a, NodePayloadType>>,

    finished: CallBackType,

    node_states: HashMap<NodeIdType, NodeState>,

    queue: VecDeque<(Option<EdgeIdType>, NodeIdType)>,
}

impl<'a, EdgePayloadType, NodePayloadType, CallBackType>
    BreadthFirstIterator<'a, EdgePayloadType, NodePayloadType, CallBackType>
where
    EdgePayloadType: PartialEq,
    NodePayloadType: PartialEq,
    CallBackType: FnMut(&NodeType<'a, NodePayloadType>),
{
    pub fn new(
        source_node_id: NodeIdType,
        edges: &'a HashMap<EdgeIdType, EdgeType<'a, EdgePayloadType>>,
        nodes: &'a HashMap<NodeIdType, NodeType<'a, NodePayloadType>>,
        finished: CallBackType,
    ) -> Self
    where
        CallBackType: FnMut(&NodeType<'a, NodePayloadType>),
    {
        let node_states: HashMap<NodeIdType, NodeState> = nodes
            .keys()
            .map(|node_id| (*node_id, NodeState::Undiscovered))
            .collect();
        let queue: VecDeque<(Option<EdgeIdType>, NodeIdType)> =
            vec![(None, source_node_id)].into_iter().collect();

        BreadthFirstIterator {
            source_node_id,
            edges,
            nodes,
            finished,
            node_states,
            queue,
        }
    }
}

impl<'a, EdgePayloadType, NodePayloadType, CallBackType> Iterator
    for BreadthFirstIterator<'a, EdgePayloadType, NodePayloadType, CallBackType>
where
    EdgePayloadType: PartialEq,
    NodePayloadType: PartialEq,
    CallBackType: FnMut(&NodeType<'a, NodePayloadType>),
{
    type Item = (Option<EdgeIdType>, NodeIdType);

    fn next(&mut self) -> Option<(Option<EdgeIdType>, NodeIdType)> {
        if !self.queue.is_empty() {
            let (via, from) = self.queue.pop_back().unwrap();

            for edge_id in self.nodes[&from].outgoing_of().into_iter() {
                let to = self.edges[edge_id].vertices_of().1;

                if *(self.node_states.get(&to).unwrap()) != NodeState::Finished {
                    *(self.node_states.get_mut(&to).unwrap()) = NodeState::Discovered;
                    self.queue.push_front((Some(*edge_id), to));
                }
            }

            self.node_states.insert(from, NodeState::Finished);

            Some((via, from))
        } else {
            None
        }
    }
}

/* ------------------------------------------------------------------------
 * DEPTH FIRST ITERATOR
 */
#[derive(Debug)]
pub struct DepthFirstIterator<'a, EdgePayloadType, NodePayloadType, CallBackType>
where
    EdgePayloadType: PartialEq,
    NodePayloadType: PartialEq,
    CallBackType: FnMut(&NodeType<'a, NodePayloadType>),
{
    source_node_id: NodeIdType,
    edges: &'a HashMap<EdgeIdType, EdgeType<'a, EdgePayloadType>>,
    nodes: &'a HashMap<NodeIdType, NodeType<'a, NodePayloadType>>,

    finished: CallBackType,

    node_states: HashMap<NodeIdType, NodeState>,

    stack: Vec<StackItemType<'a>>,
}

impl<'a, EdgePayloadType, NodePayloadType, CallBackType>
    DepthFirstIterator<'a, EdgePayloadType, NodePayloadType, CallBackType>
where
    EdgePayloadType: PartialEq,
    NodePayloadType: PartialEq,
    CallBackType: FnMut(&NodeType<'a, NodePayloadType>),
{
    pub fn new(
        source_node_id: NodeIdType,
        edges: &'a HashMap<EdgeIdType, EdgeType<'a, EdgePayloadType>>,
        nodes: &'a HashMap<NodeIdType, NodeType<'a, NodePayloadType>>,
        finished: CallBackType,
    ) -> Self
    where
        CallBackType: FnMut(&NodeType<'a, NodePayloadType>),
    {
        let node_states: HashMap<NodeIdType, NodeState> = nodes
            .keys()
            .map(|node_id| (*node_id, NodeState::Undiscovered))
            .collect();

        let stack_item = StackItemType {
            origin: None,
            targets: vec![TargetItemType {
                via: None,
                target: source_node_id,
            }],
        };
        let stack: Vec<StackItemType> = vec![stack_item];

        DepthFirstIterator {
            source_node_id,
            edges,
            nodes,
            finished,
            node_states,
            stack,
        }
    }

    fn targets_of(&self, node: NodeIdType) -> Vec<TargetItemType<'a>> {
        self.nodes[&node]
            .outgoing_of()
            .iter()
            .map(|edge| TargetItemType {
                via: Some(*edge),
                target: self.edges[edge].vertices_of().1,
            })
            .collect()
    }
}

impl<'a, EdgePayloadType, NodePayloadType, CallBackType> Iterator
    for DepthFirstIterator<'a, EdgePayloadType, NodePayloadType, CallBackType>
where
    EdgePayloadType: PartialEq,
    NodePayloadType: PartialEq,
    CallBackType: FnMut(&NodeType<'a, NodePayloadType>),
{
    type Item = Result<(Option<EdgeIdType>, NodeIdType), String>;

    fn next(&mut self) -> Option<Result<(Option<EdgeIdType>, NodeIdType), String>> {
        while !self.stack.is_empty() {
            let stack_item = self.stack.last_mut().unwrap();
            let targets = &mut stack_item.targets;

            if !targets.is_empty() {
                let target_item = targets.remove(0);
                let to = target_item.target;

                if *(self.node_states.get(&to).unwrap()) == NodeState::Discovered {
                    return Some(Err(format!("Detected a cycle at node {:?}!", to)));
                } else if *(self.node_states.get(&to).unwrap()) == NodeState::Undiscovered {
                    *(self.node_states.get_mut(&to).unwrap()) = NodeState::Discovered;
                    self.stack.push(StackItemType {
                        origin: Some(to),
                        targets: self.targets_of(to),
                    });
                    return Some(Ok((target_item.via.copied(), to)));
                }
            } else if let Some(node) = self.stack.pop().unwrap().origin {
                (self.finished)(&self.nodes.get(&node).unwrap());
                self.node_states.insert(node, NodeState::Finished);
            }
        }

        None
    }
}

/* ------------------------------------------------------------------------
 * STACK ITEM TYPE ... This is a helper struct used in depth_first(), to (hopefully) clarify the code.
 */
#[derive(Debug)]
struct StackItemType<'a> {
    origin: Option<NodeIdType>,
    targets: Vec<TargetItemType<'a>>,
}

/* ------------------------------------------------------------------------
 * TARGET ITEM TYPE ... This is a helper struct used in depth_first(), to (hopefully) clarify the code.
 */
#[derive(Debug)]
struct TargetItemType<'a> {
    via: Option<&'a EdgeIdType>,
    target: NodeIdType,
}

/* ------------------------------------------------------------------------
 * CONVENIENCE TYPES
 */
type EdgeIdsType = Vec<Option<EdgeIdType>>;
type NodeIdsType = Vec<NodeIdType>;

/* ------------------------------------------------------------------------
 * UNIT TESTS
 */
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn name_001() {
        let correct_name = "CORRECT";
        let incorrect_name = "INCORRECT";
        let graph = GraphType::<(), ()>::new(correct_name);

        assert_eq!(graph.name, correct_name);
        assert_ne!(graph.name, incorrect_name);
    }

    #[test]
    fn add_node_001() {
        let name = "GRAPH";
        let mut graph: GraphType<(), &str> = GraphType::new(name);
        let payloads = vec!["FIRST", "SECOND", "THIRD"];
        let node_ids: Vec<NodeIdType> = payloads
            .iter()
            .map(|payload| graph.add_node(&payload).unwrap())
            .collect();

        assert_eq!(graph.nodes.len(), payloads.len());
        for node_id in &node_ids {
            assert!(graph.nodes.contains_key(node_id));
        }
    }

    #[test]
    fn add_nodes_001() {
        let name = "GRAPH";
        let mut graph: GraphType<(), &str> = GraphType::new(name);
        let payloads = vec![&"FIRST", &"SECOND", &"THIRD"];
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
    fn add_edge_001() {
        let name = "GRAPH";
        let mut graph: GraphType<(NodeIdType, NodeIdType), &str> = GraphType::new(name);
        let node_payloads = vec![&"FIRST", &"SECOND", &"THIRD", &"FOURTH", &"FIFTH"];
        let node_ids = match graph.add_nodes(&node_payloads) {
            Ok(node_ids) => node_ids,
            Err(e) => std::panic::panic_any(e),
        };

        let mut edge_payloads = vec![];
        node_ids[1..].iter().fold(node_ids[0], |from, &to| {
            edge_payloads.push((from, to));
            to
        });

        let edge_ids: Vec<EdgeIdType> = edge_payloads
            .iter()
            .map(|payload| {
                let (from, to) = payload;
                match graph.add_edge(*from, *to, &payload) {
                    Ok(edge_id) => edge_id,
                    Err(e) => std::panic::panic_any(e),
                }
            })
            .collect();

        assert_eq!(graph.edges.len(), edge_ids.len());
        for (i, edge_id) in edge_ids.iter().enumerate() {
            assert!(graph.edges.contains_key(edge_id));

            let (from, to) = graph.edges[edge_id].vertices_of();
            assert_eq!(node_ids[i], from);
            assert_eq!(node_ids[i + 1], to);
        }
    }

    #[test]
    fn breadth_first_001() {
        let name = "TREE";
        let mut graph: GraphType<(), ()> = GraphType::new(name);
        let node_ids = (1..=10)
            .map(|_| graph.add_node(&()).unwrap())
            .collect::<Vec<NodeIdType>>();

        let edges_by_id = [
            (0, 1),
            (0, 4),
            (0, 8),
            (1, 2),
            (4, 5),
            (4, 7),
            (8, 9),
            (2, 3),
            (5, 6),
        ];
        let _edges: Vec<EdgeIdType> = edges_by_id
            .iter()
            .map(|(from, to)| graph.add_edge(node_ids[*from], node_ids[*to], &()).unwrap())
            .collect();

        let expected: Vec<NodeIdType> = vec![1, 2, 5, 9, 3, 6, 8, 10, 4, 7]
            .into_iter()
            .map(|id| NodeIdType::new(id as usize))
            .collect();

        let result: Vec<NodeIdType> = graph
            .breadth_first(node_ids[0], |_| {})
            .map(|(_, node_id)| node_id)
            .collect();

        assert_eq!(expected, result);
    }

    #[test]
    fn depth_first_001() {
        let name = "GRAPH";
        let mut graph: GraphType<(NodeIdType, NodeIdType), &str> = GraphType::new(name);
        let node_payloads = vec![&"FIRST", &"SECOND", &"THIRD", &"FOURTH", &"FIFTH"];
        let node_ids = match graph.add_nodes(&node_payloads) {
            Ok(node_ids) => node_ids,
            Err(e) => std::panic::panic_any(e),
        };

        let mut edge_payloads = vec![];
        node_ids[1..].iter().fold(node_ids[0], |from, &to| {
            edge_payloads.push((from, to));
            to
        });

        let _edge_ids: Vec<EdgeIdType> = edge_payloads
            .iter()
            .map(|payload| {
                let (from, to) = payload;
                match graph.add_edge(*from, *to, &payload) {
                    Ok(edge_id) => edge_id,
                    Err(e) => std::panic::panic_any(e),
                }
            })
            .collect();

        graph
            .depth_first(node_ids[0], |_| {})
            .enumerate()
            .for_each(|(i, result)| {
                match result {
                    Ok((_, node_id)) => assert_eq!(node_id, node_ids[i]),
                    Err(e) => std::panic::panic_any(e),
                };
            });
    }

    #[test]
    fn depth_first_002() {
        let name = "TREE";
        let mut graph: GraphType<(), ()> = GraphType::new(name);
        let node_ids = (1..=10)
            .map(|_| graph.add_node(&()).unwrap())
            .collect::<Vec<NodeIdType>>();

        let edges_by_id = [
            (0, 1),
            (0, 4),
            (0, 8),
            (1, 2),
            (4, 5),
            (4, 7),
            (8, 9),
            (2, 3),
            (5, 6),
        ];
        let _edges: Vec<EdgeIdType> = edges_by_id
            .iter()
            .map(|(from, to)| graph.add_edge(node_ids[*from], node_ids[*to], &()).unwrap())
            .collect();

        let lexicographical: Vec<NodeIdType> =
            (1..=10).map(|id| NodeIdType::new(id as usize)).collect();

        let visited: Vec<NodeIdType> = graph
            .depth_first(node_ids[0], |_| {})
            .map(|result| match result {
                Ok((_, node_id)) => node_id,
                Err(e) => std::panic::panic_any(e),
            })
            .collect();

        assert_eq!(lexicographical, visited);
    }

    #[test]
    fn depth_first_003() {
        let name = "DAG";
        let mut graph: GraphType<(), ()> = GraphType::new(name);
        let node_ids = (1..=11)
            .map(|_| graph.add_node(&()).unwrap())
            .collect::<Vec<NodeIdType>>();

        graph.add_edge(node_ids[0], node_ids[1], &()).unwrap();
        graph.add_edge(node_ids[0], node_ids[4], &()).unwrap();
        graph.add_edge(node_ids[0], node_ids[8], &()).unwrap();

        graph.add_edge(node_ids[1], node_ids[2], &()).unwrap();

        graph.add_edge(node_ids[4], node_ids[5], &()).unwrap();
        graph.add_edge(node_ids[4], node_ids[7], &()).unwrap();

        graph.add_edge(node_ids[8], node_ids[9], &()).unwrap();
        graph.add_edge(node_ids[2], node_ids[3], &()).unwrap();
        graph.add_edge(node_ids[5], node_ids[6], &()).unwrap();

        graph.add_edge(node_ids[3], node_ids[10], &()).unwrap();
        graph.add_edge(node_ids[6], node_ids[10], &()).unwrap();
        graph.add_edge(node_ids[7], node_ids[10], &()).unwrap();
        graph.add_edge(node_ids[9], node_ids[10], &()).unwrap();

        let visited_expected: Vec<NodeIdType> = [1, 2, 3, 4, 11, 5, 6, 7, 8, 9, 10]
            .iter()
            .map(|id| NodeIdType::new(*id as usize))
            .collect();

        let topological_expected: Vec<NodeIdType> = [11, 4, 3, 2, 7, 6, 8, 5, 10, 9, 1]
            .iter()
            .map(|id| NodeIdType::new(*id as usize))
            .collect();

        let mut topological_result: Vec<NodeIdType> = vec![];

        let visited_result: Vec<NodeIdType> = graph
            .depth_first(node_ids[0], |node| topological_result.push(node.id_of()))
            .map(|result| match result {
                Ok((_, node_id)) => node_id,
                Err(e) => std::panic::panic_any(e),
            })
            .collect();

        assert_eq!(topological_expected, topological_result);
        assert_eq!(visited_expected, visited_result);
    }

    #[test]
    fn depth_first_004() {
        let name = "DAG";
        let mut graph: GraphType<(), u32> = GraphType::new(name);

        let node_payloads = vec![&2, &3, &4, &5, &6, &7, &1];
        let node_ids = graph.add_nodes(&node_payloads).unwrap();

        let edges = [
            (0, 1),
            (0, 4),
            (1, 2),
            (4, 1),
            (5, 2),
            (6, 5),
            (5, 4),
            (4, 3),
        ];
        let _edges: Vec<EdgeIdType> = edges
            .iter()
            .map(|(from, to)| graph.add_edge(node_ids[*from], node_ids[*to], &()).unwrap())
            .collect();
        let expected = [2, 3, 4, 6, 5];

        let result: Vec<&u32> = graph
            .depth_first(node_ids[0], |_| {})
            .map(|result| match result {
                Ok((_, node_id)) => graph.nodes[&node_id].payload_of(),
                Err(e) => std::panic::panic_any(e),
            })
            .collect();

        expected
            .iter()
            .zip(result)
            .for_each(|(left, right)| assert_eq!(left, right));

        let expected = [1, 7, 4, 6, 3, 5];

        let result: Vec<&u32> = graph
            .depth_first(node_ids[6], |_| {})
            .map(|result| match result {
                Ok((_, node_id)) => graph.nodes[&node_id].payload_of(),
                Err(e) => std::panic::panic_any(e),
            })
            .collect();

        expected
            .iter()
            .zip(result)
            .for_each(|(left, right)| assert_eq!(left, right));
    }

    #[test]
    #[should_panic]
    fn depth_first_cycle_001() {
        let name = "CYCLE DETECTION";
        let mut graph: GraphType<(), u32> = GraphType::new(name);

        let node_payloads = vec![&2, &3, &6];
        let node_ids = graph.add_nodes(&node_payloads).unwrap();

        let edges = vec![(0, 1), (1, 2), (2, 0)];
        let _edges: Vec<EdgeIdType> = edges
            .iter()
            .map(|(from, to)| graph.add_edge(node_ids[*from], node_ids[*to], &()).unwrap())
            .collect();

        graph
            .depth_first(node_ids[0], |_| {})
            .for_each(|result| match result {
                Ok((_, _)) => (),
                Err(e) => std::panic::panic_any(e),
            });
    }

    #[test]
    fn shortest_path_01() {
        let name = "SHORTEST PATH";
        let mut graph: GraphType<u32, u32> = GraphType::new(name);
        let node_payloads = vec![&1, &2, &3, &4, &5, &6, &7, &8, &9, &10, &11];
        let node_ids = match graph.add_nodes(&node_payloads) {
            Ok(node_ids) => node_ids,
            Err(e) => std::panic::panic_any(e),
        };

        let edges_by_id = vec![
            (0, 1, 1, 1),
            (0, 4, 2, 2),
            (0, 8, 5, 5),
            (1, 2, 6, 6),
            (4, 5, 3, 3),
            (4, 7, 4, 4),
            (8, 9, 7, 7),
            (2, 3, 1, 1),
            (5, 6, 2, 2),
            (3, 10, 1, 1),
            (6, 10, 3, 3),
            (7, 10, 5, 5),
            (9, 10, 3, 3),
        ];

        let _edge_ids: Vec<EdgeIdType> = edges_by_id
            .iter()
            .map(|(from, to, payload, weight)| {
                let edge_id = graph
                    .add_edge(node_ids[*from], node_ids[*to], payload)
                    .unwrap();
                graph
                    .edges
                    .get_mut(&edge_id)
                    .unwrap()
                    .weight(*weight as f64);

                edge_id
            })
            .collect();

        let source_node_id = node_ids[0];
        let target_node_id = node_ids[10];

        let expected_path = vec![
            node_ids[0],
            node_ids[1],
            node_ids[2],
            node_ids[3],
            node_ids[10],
        ];
        let expected_cost = 9.0;

        // shortest_path() needs node IDs in the reverse of depth-first ... in other words in topologically-sorted
        // order.
        let sorted: Vec<NodeIdType> = graph
            .depth_first(source_node_id, |_| {})
            .map(|result| match result {
                Ok((_, node_id)) => node_id,
                Err(e) => std::panic::panic_any(e),
            })
            .collect::<Vec<NodeIdType>>()
            .into_iter()
            .rev()
            .collect();

        let (result_cost, result_edges, result_path) = graph
            .shortest_path(&sorted, &source_node_id, &target_node_id)
            .unwrap();

        assert!((expected_cost - result_cost).abs() < f64::EPSILON);
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
