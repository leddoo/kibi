use core::num::NonZeroU32;


#[allow(dead_code)] // @temp
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Key {
    Counter,
    U64     (u64),
    String  (String),
}

impl Default for Key {
    #[inline(always)]
    fn default() -> Self { Key::Counter }
}


#[derive(Debug, Default)]
pub struct Props {
    pub text: String,
}



#[derive(Debug, PartialEq, Eq, Hash)]
enum KeyData {
    Counter (u32),
    U64     (u64),
    String  (String),
}

type OptNodeId = Option<NonZeroU32>;


#[derive(Debug)]
struct Node {
    // identity.
    key:       KeyData,
    counter:   u32,
    hash_next: OptNodeId,

    // content.
    props: Props,

    // hierarchy.
    parent:       u32,
    next_sibling: OptNodeId,
    prev_sibling: OptNodeId,
    first_child:  OptNodeId,
    last_child:   OptNodeId,
}

impl Node {
    #[inline(always)]
    fn next_counter_key(&mut self) -> KeyData {
        let value = self.counter;
        self.counter += 1;
        KeyData::Counter(value)
    }

    #[inline(always)]
    fn global_key(&self) -> (u32, &KeyData) {
        (self.parent, &self.key)
    }

    #[inline(always)]
    fn begin(&mut self, props: Props) {
        self.counter = 0;
        self.props = props;
        self.first_child = None;
        self.last_child  = None;
    }
}



#[derive(Debug)]
pub struct Gui {
    nodes:   Vec<Node>,
    hash:    Vec<OptNodeId>,
    current_parent: usize,
}

impl Gui {
    pub fn new() -> Gui {
        let root = Node {
            key:       KeyData::Counter(0),
            counter:   0,
            hash_next: None,

            props: Default::default(),

            parent:       0,
            next_sibling: None,
            prev_sibling: None,
            first_child:  None,
            last_child:   None,
        };

        Gui {
            nodes:   vec![root],
            hash:    vec![None; 16],
            current_parent: usize::MAX,
        }
    }


    pub fn begin(&mut self) {
        assert_eq!(self.current_parent, usize::MAX);
        self.current_parent = 0;
        self.nodes[0].begin(Props::default());
    }

    pub fn end(&mut self) {
        assert_eq!(self.current_parent, 0);
        self.current_parent = usize::MAX;
    }


    fn hash(global_key: (u32, &KeyData)) -> u64 {
        use core::hash::{Hash, Hasher};

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        global_key.hash(&mut hasher);
        hasher.finish()
    }

    pub fn node<F: FnOnce(&mut Gui)>(&mut self, key: Key, props: Props, f: F) {
        let key = match key {
            Key::Counter       => self.nodes[self.current_parent].next_counter_key(),
            Key::U64(value)    => KeyData::U64(value),
            Key::String(value) => KeyData::String(value),
        };

        let global_key = (self.current_parent as u32, &key);
        let hash = Self::hash(global_key);

        let mut node = None;

        // probe hash table.
        {
            let slot = hash as usize & (self.hash.len() - 1);
            let mut at = self.hash[slot];
            while let Some(current) = at {
                let curr = &mut self.nodes[current.get() as usize];
                if curr.global_key() == global_key {
                    node = at;
                    break;
                }
                at = curr.hash_next;
            }
        }

        let node = match node {
            // found match.
            Some(node) => {
                println!("found match for {:?}: {}", global_key, node);
                self.nodes[node.get() as usize].begin(props);
                node
            }

            // was new.
            None => {
                println!("no match for {:?}", global_key);

                // allocate node.
                let node = NonZeroU32::new(self.nodes.len() as u32).unwrap();

                // grow hash table.
                if self.nodes.len() + 1 > self.hash.len() {
                    //let mut new_hash = vec![None; 2*self.hash.len()];
                    //self.hash = new_hash;
                    unimplemented!();
                }

                // insert into hash table.
                let slot = hash as usize & (self.hash.len() - 1);
                let hash_next = self.hash[slot];
                self.hash[slot] = Some(node);

                self.nodes.push(Node {
                    key,
                    counter: 0,
                    hash_next,

                    props,

                    parent:       self.current_parent as u32,
                    next_sibling: None,
                    prev_sibling: None,
                    first_child:  None,
                    last_child:   None,
                });

                node
            }
        };

        // append to parent's child list.
        self.nodes[node.get() as usize].prev_sibling = {
            let parent = &mut self.nodes[self.current_parent];

            let prev_last = parent.last_child;
            parent.last_child = Some(node);

            if let Some(last) = prev_last {
                self.nodes[last.get() as usize].next_sibling = Some(node);
                Some(last)
            }
            else {
                parent.first_child = Some(node);
                None
            }
        };

        // process children.
        let old_parent = self.current_parent;
        self.current_parent = node.get() as usize;
        f(self);
        self.current_parent = old_parent;
    }
}

