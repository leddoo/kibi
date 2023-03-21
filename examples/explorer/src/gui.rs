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

    pub pointer_events: bool,
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

    #[inline(always)]
    pub fn with_pointer_events(mut self) -> Self {
        self.pointer_events = true;
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

            pointer_events: false,
        }
    }
}



#[derive(Debug, PartialEq, Eq, Hash)]
enum KeyData {
    Counter (u32),
    U64     (u64),
    String  (String),
}


struct Widget {
    // identity.
    key:       KeyData,
    counter:   u32,
    hash_next: OptWidgetId,

    // content.
    props: Props,

    // hierarchy.
    parent:       u32,
    next_sibling: OptWidgetId,
    prev_sibling: OptWidgetId,
    first_child:  OptWidgetId,
    last_child:   OptWidgetId,

    // layout.
    pos:  [f32; 2],
    size: [f32; 2],
    text_layout: TextLayout<u32>,
}

type OptWidgetId = Option<NonZeroU32>;


impl Widget {
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



#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WidgetId(u32);


#[derive(Clone, Copy, Debug)]
pub struct WidgetEvents {
    pub prev_hovered:   bool,
    pub hovered:        bool,
    pub prev_active:    bool,
    pub active:         bool,
}

impl WidgetEvents {
    #[inline(always)]
    pub fn clicked(&self) -> bool {
        self.prev_active && !self.active && self.hovered
    }
}


pub struct Gui {
    widgets: Vec<Widget>,
    hash:    Vec<OptWidgetId>,
    current_parent: usize,

    fonts: FontCtx,

    mouse_pos:  [f32; 2],
    mouse_down: bool,

    prev_hovered: u32,
    hovered:      u32,
    prev_active:  u32,
    active:       u32,
}

impl Gui {
    pub fn new(fonts: &FontCtx) -> Gui {
        let root = Widget {
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
            widgets:   vec![root],
            hash:    vec![None; 16],
            current_parent: usize::MAX,

            fonts: fonts.clone(),

            mouse_pos:  [0.; 2],
            mouse_down: false,

            prev_hovered: 0,
            hovered:      0,
            prev_active:  0,
            active:       0,
        }
    }


    pub fn hit_test(&mut self, x: f32, y: f32) -> Option<WidgetId> {
        fn rec(this: &mut Gui, widget_index: usize, x: f32, y: f32) -> Option<WidgetId> {
            let widget = &this.widgets[widget_index];

            if x < widget.pos[0] || x >= widget.pos[0] + widget.size[0]
            || y < widget.pos[1] || y >= widget.pos[1] + widget.size[1] {
                return None;
            }

            let xx = x - widget.pos[0];
            let yy = y - widget.pos[0];

            let mut at = widget.first_child;
            while let Some(current) = at {
                let current = current.get() as usize;
                let result = rec(this, current, xx, yy);
                if result.is_some() {
                    return result;
                }

                at = this.widgets[current].next_sibling;
            }

            return Some(WidgetId(widget_index as u32));
        }

        rec(self, 0, x, y)
    }


    pub fn begin(&mut self) {
        assert_eq!(self.current_parent, usize::MAX);
        self.current_parent = 0;
        self.widgets[0].begin(Props::default());
    }

    pub fn end(&mut self) {
        assert_eq!(self.current_parent, 0);
        self.current_parent = usize::MAX;

        self.prev_hovered = self.hovered;
        self.prev_active  = self.active;
    }


    fn hash(global_key: (u32, &KeyData)) -> u64 {
        use core::hash::{Hash, Hasher};

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        global_key.hash(&mut hasher);
        hasher.finish()
    }

    pub fn widget<F: FnOnce(&mut Gui)>(&mut self, key: Key, props: Props, f: F) -> WidgetEvents {
        let key = match key {
            Key::Counter       => self.widgets[self.current_parent].next_counter_key(),
            Key::U64(value)    => KeyData::U64(value),
            Key::String(value) => KeyData::String(value),
        };

        let global_key = (self.current_parent as u32, &key);
        let hash = Self::hash(global_key);

        let mut widget = None;

        // probe hash table.
        {
            let slot = hash as usize & (self.hash.len() - 1);
            let mut at = self.hash[slot];
            while let Some(current) = at {
                let curr = &mut self.widgets[current.get() as usize];
                if curr.global_key() == global_key {
                    widget = at;
                    break;
                }
                at = curr.hash_next;
            }
        }

        let widget = match widget {
            // found match.
            Some(widget) => {
                self.widgets[widget.get() as usize].begin(props);
                widget
            }

            // was new.
            None => {
                // allocate widget.
                let widget = NonZeroU32::new(self.widgets.len() as u32).unwrap();

                // grow hash table.
                if self.widgets.len() + 1 > self.hash.len() {
                    //let mut new_hash = vec![None; 2*self.hash.len()];
                    //self.hash = new_hash;
                    unimplemented!();
                }

                // insert into hash table.
                let slot = hash as usize & (self.hash.len() - 1);
                let hash_next = self.hash[slot];
                self.hash[slot] = Some(widget);

                self.widgets.push(Widget {
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

                widget
            }
        };

        // append to parent's child list.
        self.widgets[widget.get() as usize].prev_sibling = {
            let parent = &mut self.widgets[self.current_parent];

            let prev_last = parent.last_child;
            parent.last_child = Some(widget);

            if let Some(last) = prev_last {
                self.widgets[last.get() as usize].next_sibling = Some(widget);
                Some(last)
            }
            else {
                parent.first_child = Some(widget);
                None
            }
        };

        // process children.
        let old_parent = self.current_parent;
        self.current_parent = widget.get() as usize;
        f(self);
        self.current_parent = old_parent;

        let prev_hovered = self.prev_hovered == widget.get();
        let hovered      = self.hovered      == widget.get();
        let prev_active  = self.prev_active  == widget.get();
        let active       = self.active       == widget.get();
        WidgetEvents {
            prev_hovered, hovered,
            prev_active,  active,
        }
    }


    pub fn layout(&mut self) {
        fn rec(this: &mut Gui, widget_index: usize) {
            let widget = &this.widgets[widget_index];

            let mut width  = widget.text_layout.width();
            let mut height = widget.text_layout.height();
            let mut cursor = 0f32;

            let mut at = widget.first_child;
            while let Some(current) = at {
                let current = current.get() as usize;
                rec(this, current);

                let child = &mut this.widgets[current];
                child.pos = [0., cursor];

                width   = width.max(child.size[0]);
                cursor += child.size[1];

                at = child.next_sibling;
            }

            height = height.max(cursor);

            this.widgets[widget_index].size = [width, height];
        }

        rec(self, 0);
    }


    pub fn render(&mut self, r: &mut Renderer) {
        fn rec(this: &mut Gui, widget_index: usize, px: i32, py: i32, r: &mut Renderer) {
            let widget = &this.widgets[widget_index];

            let [x0, y0] = widget.pos;
            let x1 = x0 + widget.size[0];
            let y1 = y0 + widget.size[1];

            let x0 = px + x0 as i32;
            let y0 = py + y0 as i32;
            let x1 = px + x1 as i32;
            let y1 = py + y1 as i32;

            if widget.props.fill {
                r.fill_rect_abs(x0, y0, x1, y1, widget.props.fill_color);
            }

            r.draw_text_layout_abs(x0, y0, &widget.text_layout);

            let mut at = widget.first_child;
            while let Some(current) = at {
                let current = current.get() as usize;
                rec(this, current, x0, y0, r);

                at = this.widgets[current].next_sibling;
            }
        }

        rec(self, 0,  0, 0,  r);
    }


    pub fn update<F: FnOnce(&mut Gui) -> bool>(&mut self, f: F) -> bool {
        self.begin();
        let result = f(self);
        self.end();
        self.layout();
        result
    }


    pub fn mouse_move(&mut self, mx: f32, my: f32) -> bool {
        if mx == self.mouse_pos[0] && my == self.mouse_pos[1] {
            return false;
        }
        self.mouse_pos = [mx, my];

        let hit = self.hit_test(mx, my);
        let hit = hit.filter(|hit| self.widgets[hit.0 as usize].props.pointer_events);
        if let Some(hit) = hit {
            self.hovered = hit.0;
        }
        else {
            self.hovered = 0;
        }
        return true;
    }

    pub fn mouse_down(&mut self, is_down: bool) -> bool {
        if is_down == self.mouse_down {
            return false;
        }
        self.mouse_down = is_down;

        if is_down {
            self.active = self.hovered;
        }
        else {
            self.active = 0;
        }
        return true;
    }
}

