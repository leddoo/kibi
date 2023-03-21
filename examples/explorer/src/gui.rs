use core::num::NonZeroU32;
use crate::renderer::*;


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


#[derive(Debug)]
pub struct Props {
    pub font_face: FaceId,
    pub font_size: f32,
    pub text_color: u32,
    pub text: String,

    pub fill: bool,
    pub fill_color: u32,
}

impl Props {
    #[inline(always)]
    pub fn new() -> Props { Props::default() }

    #[inline(always)]
    pub fn with_text(mut self, text: String) -> Self {
        self.text = text;
        self
    }

    #[inline(always)]
    pub fn with_fill(mut self, color: u32) -> Self {
        self.fill       = true;
        self.fill_color = color;
        self
    }
}

impl Default for Props {
    #[inline(always)]
    fn default() -> Self {
        Props {
            font_face: FaceId::DEFAULT,
            font_size: 16.0,
            text_color: 0xFFBFBDB6,
            text: String::new(),

            fill: false,
            fill_color: 0,
        }
    }
}



#[derive(Debug, PartialEq, Eq, Hash)]
enum KeyData {
    Counter (u32),
    U64     (u64),
    String  (String),
}

type OptNodeId = Option<NonZeroU32>;


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

    // layout.
    pos:  [f32; 2],
    size: [f32; 2],
    text_layout: TextLayout<u32>,
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

        self.text_layout.clear();
        self.text_layout.append_ex(&self.props.text, self.props.font_face, self.props.font_size, self.props.text_color);
    }
}



pub struct Gui {
    nodes:   Vec<Node>,
    hash:    Vec<OptNodeId>,
    current_parent: usize,

    fonts: FontCtx,
}

impl Gui {
    pub fn new(fonts: &FontCtx) -> Gui {
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

            pos:  [0.0; 2],
            size: [0.0; 2],
            text_layout: TextLayout::new(fonts),
        };

        Gui {
            nodes:   vec![root],
            hash:    vec![None; 16],
            current_parent: usize::MAX,
            fonts: fonts.clone(),
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
                self.nodes[node.get() as usize].begin(props);
                node
            }

            // was new.
            None => {
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

                    pos:  [0.0; 2],
                    size: [0.0; 2],
                    text_layout: TextLayout::new(&self.fonts),
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


    pub fn layout(&mut self) {
        fn rec(this: &mut Gui, node_index: usize) {
            let node = &this.nodes[node_index];

            let mut width  = node.text_layout.width();
            let mut height = node.text_layout.height();
            let mut cursor = 0f32;

            let mut at = node.first_child;
            while let Some(current) = at {
                let current = current.get() as usize;
                rec(this, current);

                let child = &mut this.nodes[current];
                child.pos = [0., cursor];

                width   = width.max(child.size[0]);
                cursor += child.size[1];

                at = child.next_sibling;
            }

            height = height.max(cursor);

            this.nodes[node_index].size = [width, height];
        }

        rec(self, 0);
    }


    pub fn render(&mut self, r: &mut Renderer) {
        fn rec(this: &mut Gui, node_index: usize, px: i32, py: i32, r: &mut Renderer) {
            let node = &this.nodes[node_index];

            let [x0, y0] = node.pos;
            let x1 = x0 + node.size[0];
            let y1 = y0 + node.size[1];

            let x0 = px + x0 as i32;
            let y0 = py + y0 as i32;
            let x1 = px + x1 as i32;
            let y1 = py + y1 as i32;

            if node.props.fill {
                r.fill_rect_abs(x0, y0, x1, y1, node.props.fill_color);
            }

            r.draw_text_layout_abs(x0, y0, &node.text_layout);

            let mut at = node.first_child;
            while let Some(current) = at {
                let current = current.get() as usize;
                rec(this, current, x0, y0, r);

                at = this.nodes[current].next_sibling;
            }
        }

        rec(self, 0,  0, 0,  r);
    }
}

