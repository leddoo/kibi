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


#[allow(dead_code)] // @temp
#[derive(Clone, Copy, Debug)]
pub enum Layout {
    None,
    Flow,
    Flex(FlexLayout),
}

impl Default for Layout { #[inline(always)] fn default() -> Self { Layout::Flow } }

impl Layout {
    #[inline(always)]
    fn is_flow(&self) -> bool { if let Layout::Flow = self { true } else { false } }
}


#[allow(dead_code)] // @temp
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FlexDirection {
    Row,
    Column,
}

impl Default for FlexDirection { #[inline(always)] fn default() -> Self { FlexDirection::Row } }

impl FlexDirection {
    #[inline(always)]
    pub fn main_axis(self) -> usize {
        match self {
            FlexDirection::Row    => 0,
            FlexDirection::Column => 1,
        }
    }

    #[inline(always)]
    pub fn cross_axis(self) -> usize {
        match self {
            FlexDirection::Row    => 1,
            FlexDirection::Column => 0,
        }
    }
}


#[allow(dead_code)] // @temp
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FlexJustify {
    // @todo: "Align(f32)" instead? and constructors for begin/center/end.
    Begin,
    Center,
    End,
    SpaceBetween,
    SpaceEvenly,
}

impl Default for FlexJustify { #[inline(always)] fn default() -> Self { FlexJustify::Begin } }


#[allow(dead_code)] // @temp
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FlexAlign {
    // @todo: "Align(f32)" instead? and constructors for begin/center/end.
    Begin,
    Center,
    End,
    // @todo: Baseline,
    Stretch,
}

impl Default for FlexAlign { #[inline(always)] fn default() -> Self { FlexAlign::Stretch } }


#[derive(Clone, Copy, Debug, Default)]
pub struct FlexLayout {
    pub direction: FlexDirection,
    pub justify:   FlexJustify,
    pub align:     FlexAlign,
}


#[derive(Clone, Debug)]
pub struct Props {
    pub layout: Layout,

    pub size: [Option<f32>; 2],
    pub flex_grow: f32,

    pub font_face: FaceId,
    pub font_size: f32,
    pub text_color: u32,

    pub fill: bool,
    pub fill_color: u32,

    pub pointer_events: bool,
}

impl Props {
    #[inline(always)]
    pub fn new() -> Props { Props::default() }

    #[allow(dead_code)] // @temp
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
            layout: Layout::default(),

            size: [None; 2],
            flex_grow: 0.,

            font_face: FaceId::DEFAULT,
            font_size: 16.0,
            text_color: 0xFFBFBDB6,

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
    TextLayout(u32),
}


struct Widget {
    // identity.
    gen:       u64,
    key:       KeyData,
    hash_prev: OptWidgetId,
    hash_next: OptWidgetId,

    // content.
    props: Props,
    data:  WidgetData,

    // hierarchy.
    parent:        u32,
    prev_sibling:  OptWidgetId,
    next_sibling:  OptWidgetId,
    prev_render_sibling: OptWidgetId,
    next_render_sibling: OptWidgetId,

    // layout.
    pos:  [f32; 2],
    size: [f32; 2],
    content_size:   [f32; 2],
    intrinsic_size: [f32; 2],
}

enum WidgetData {
    Box        (BoxData),
    TextLayout (TextLayoutData),
    Text       (TextData),
    Free       (OptWidgetId),
}

impl WidgetData {
    #[inline(always)]
    fn is_free(&self) -> bool { if let WidgetData::Free(_) = self { true } else { false } }
}


#[derive(Clone, Copy)]
struct BoxData {
    first_child:        OptWidgetId,
    last_child:         OptWidgetId,
    first_render_child: OptWidgetId,
    last_render_child:  OptWidgetId,
}

impl BoxData {
    #[inline(always)]
    fn default() -> BoxData {
        BoxData { first_child: None, last_child: None, first_render_child: None, last_render_child: None }
    }
}


struct TextLayoutData {
    layout: TextLayout,
}

struct TextData {
    text: String,
}

// @todo: use an id.
type OptWidgetId = Option<NonZeroU32>;


impl Widget {
    #[inline(always)]
    fn global_key(&self) -> (u32, &KeyData) {
        (self.parent, &self.key)
    }

    #[inline(always)]
    fn begin(&mut self, gen: u64, props: Props, data: WidgetData) {
        self.gen   = gen;
        self.props = props;
        self.data  = data;
        self.prev_sibling = None;
        self.next_sibling = None;
        self.prev_render_sibling = None;
        self.next_render_sibling = None;
    }

    #[inline(always)]
    fn box_data(&mut self) -> &mut BoxData {
        match &mut self.data {
            WidgetData::Box(boks) => boks,
            _ => unreachable!()
        }
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
    gen:        u64,
    widgets:    Vec<Widget>,
    first_free: OptWidgetId,
    hash:       Vec<OptWidgetId>,

    current_parent:  usize,
    current_counter: u32,

    fonts: FontCtx,

    root_size:  [f32; 2],
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
            gen:       1,
            key:       KeyData::Counter(0),
            hash_prev: None,
            hash_next: None,

            props: Default::default(),
            data:  WidgetData::Box(BoxData::default()),

            parent:       0,
            prev_sibling: None,
            next_sibling: None,
            prev_render_sibling: None,
            next_render_sibling: None,

            pos:  [0.0; 2],
            size: [0.0; 2],
            content_size:   [0.0; 2],
            intrinsic_size: [0.0; 2],
        };

        Gui {
            gen:        1,
            widgets:    vec![root],
            first_free: None,
            hash:       vec![None; 16*1024], // @temp

            current_parent:  usize::MAX,
            current_counter: 0,

            fonts: fonts.clone(),

            root_size:  [0.0; 2],
            mouse_pos:  [0.0; 2],
            mouse_down: false,

            prev_hovered: 0,
            hovered:      0,
            prev_active:  0,
            active:       0,
        }
    }


    pub fn hit_test_filtered<F: FnMut(usize) -> bool>(&self, x: f32, y: f32, mut f: F) -> Option<WidgetId> {
        fn rec<F: FnMut(usize) -> bool>(this: &Gui, widget_index: usize, x: f32, y: f32, f: &mut F) -> Option<WidgetId> {
            let widget = &this.widgets[widget_index];

            if x < widget.pos[0] || x >= widget.pos[0] + widget.size[0]
            || y < widget.pos[1] || y >= widget.pos[1] + widget.size[1] {
                return None;
            }

            let xx = x - widget.pos[0];
            let yy = y - widget.pos[1];

            let result = match &widget.data {
                WidgetData::Box(data) => {
                    let mut at = data.first_render_child;
                    while let Some(current) = at {
                        let current = current.get() as usize;
                        let result = rec(this, current, xx, yy, f);
                        if result.is_some() {
                            return result;
                        }

                        at = this.widgets[current].next_render_sibling;
                    }

                    Some(WidgetId(widget_index as u32))
                }

                WidgetData::TextLayout(data) => {
                    let hit = data.layout.hit_test_pos(xx, yy);
                    hit.source.map(|hit| WidgetId(hit))
                }

                WidgetData::Text(_) | WidgetData::Free(_) => unreachable!()
            };

            result.filter(|widget| f(widget.0 as usize))
        }

        rec(self, 0, x, y, &mut f)
    }


    pub fn begin(&mut self, root_props: Props) {
        self.gen += 1;

        assert_eq!(self.current_parent, usize::MAX);
        self.current_parent  = 0;
        self.current_counter = 0;

        self.widgets[0].begin(self.gen, root_props, WidgetData::Box(BoxData::default()));
    }

    pub fn end(&mut self) {
        assert_eq!(self.current_parent, 0);
        self.render_children();
        self.current_parent = usize::MAX;

        self.prev_hovered = self.hovered;
        self.prev_active  = self.active;

        let mut first_free = None;
        for index in (0..self.widgets.len()).rev() {
            let widget = &mut self.widgets[index];
            if widget.gen == self.gen { continue }
            debug_assert!(widget.gen < self.gen);

            let id = NonZeroU32::new(index as u32).unwrap();
            let was_free = widget.data.is_free();

            // insert into free list.
            widget.data = WidgetData::Free(first_free);
            first_free = Some(id);

            // remove from hash table.
            if !was_free {
                let hash_prev = widget.hash_prev;
                let hash_next = widget.hash_next;
                widget.hash_prev = None;
                widget.hash_next = None;

                if let Some(prev) = hash_prev {
                    let prev = &mut self.widgets[prev.get() as usize];
                    debug_assert_eq!(prev.hash_next, Some(id));
                    prev.hash_next = hash_next;
                }
                else {
                    let hash = Self::hash((widget.parent, &widget.key));
                    let slot = hash as usize & (self.hash.len() - 1);
                    debug_assert_eq!(self.hash[slot], Some(id));
                    self.hash[slot] = hash_next;
                }

                if let Some(next) = hash_next {
                    let next = &mut self.widgets[next.get() as usize];
                    debug_assert_eq!(next.hash_prev, Some(id));
                    next.hash_prev = hash_prev;
                }
            }
        }
        self.first_free = first_free;

        #[cfg(debug_assertions)]
        self.validate();
    }


    fn validate(&self) {
        fn validate_list
            <Prev: Fn(&Widget) -> OptWidgetId, Next: Fn(&Widget) -> OptWidgetId>
            (gui: &Gui, first: OptWidgetId, expected_last: Option<OptWidgetId>, prev: Prev, next: Next)
        {
            let mut previous = None;
            let mut at = first;
            while let Some(current) = at {
                let widget = &gui.widgets[current.get() as usize];
                if prev(widget) != previous {
                    assert!(false);
                }
                assert_eq!(prev(widget), previous);
                previous = at;
                at = next(widget);
            }
            if let Some(last) = expected_last {
                assert_eq!(previous, last);
            }
        }

        fn validate_tree(gui: &Gui, index: usize) {
            let widget = &gui.widgets[index];
            match &widget.data {
                WidgetData::Box(data) => {
                    let data = *data;
                    validate_list(gui, data.first_child, Some(data.last_child),
                        |w| w.prev_sibling, |w| w.next_sibling);
                    validate_list(gui, data.first_render_child, Some(data.last_render_child),
                        |w| w.prev_render_sibling, |w| w.next_render_sibling);
                }

                WidgetData::TextLayout(_) => {}

                WidgetData::Text(_) => {
                    // @temp
                    assert_eq!(widget.prev_render_sibling, None);
                    assert_eq!(widget.next_render_sibling, None);
                }

                WidgetData::Free(_) => {
                    assert_eq!(widget.hash_prev, None);
                    assert_eq!(widget.hash_next, None);
                    assert_eq!(widget.next_sibling, None);
                    assert_eq!(widget.prev_sibling, None);
                    assert_eq!(widget.next_sibling, None);
                    assert_eq!(widget.prev_render_sibling, None);
                    assert_eq!(widget.next_render_sibling, None);
                }
            }
        }

        validate_tree(self, 0);

        // validate free list.
        {
            let mut at = self.first_free;
            while let Some(current) = at {
                let WidgetData::Free(next) = self.widgets[current.get() as usize].data else { unreachable!() };
                at = next;
            }
        }

        // validate hash map.
        for i in 0..self.hash.len() {
            validate_list(self, self.hash[i], None,
                |w| w.hash_prev,
                |w| {
                    let hash = Self::hash((w.parent, &w.key));
                    let slot = hash as usize & (self.hash.len() - 1);
                    assert_eq!(slot, i);
                    w.hash_next
                });
        }
    }


    fn hash(global_key: (u32, &KeyData)) -> u64 {
        use core::hash::{Hash, Hasher};

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        global_key.hash(&mut hasher);
        hasher.finish()
    }

    fn alloc_widget(&mut self, key: KeyData, props: Props, data: WidgetData) -> NonZeroU32 {
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
                self.widgets[widget.get() as usize].begin(self.gen, props, data);
                widget
            }

            // was new.
            None => {
                let w = Widget {
                    gen: self.gen,
                    key,
                    hash_prev: None,
                    hash_next: None,

                    props,
                    data,

                    parent:       self.current_parent as u32,
                    prev_sibling: None,
                    next_sibling: None,
                    prev_render_sibling: None,
                    next_render_sibling: None,

                    pos:  [0.0; 2],
                    size: [0.0; 2],
                    content_size:   [0.0; 2],
                    intrinsic_size: [0.0; 2],
                };

                let widget = match self.first_free {
                    Some(free) => {
                        // reuse free widget.
                        let slot = &mut self.widgets[free.get() as usize];

                        let WidgetData::Free(next_free) = slot.data else { unreachable!() };
                        self.first_free = next_free;

                        *slot = w;

                        free
                    }

                    None => {
                        // allocate widget.
                        let widget = NonZeroU32::new(self.widgets.len() as u32).unwrap();
                        self.widgets.push(w);
                        widget
                    }
                };

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
                if let Some(next) = hash_next {
                    let next = &mut self.widgets[next.get() as usize];
                    debug_assert!(next.hash_prev.is_none());
                    next.hash_prev = Some(widget);
                }
                self.widgets[widget.get() as usize].hash_next = hash_next;

                widget
            }
        };

        widget
    }

    fn new_widget(&mut self, key: KeyData, props: Props, data: WidgetData) -> NonZeroU32 {
        let widget = self.alloc_widget(key, props, data);

        // append to parent's child list.
        self.widgets[widget.get() as usize].prev_sibling = {
            let parent = &mut self.widgets[self.current_parent].box_data();

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

        widget
    }

    #[inline(always)]
    fn next_counter_key(&mut self) -> KeyData {
        let result = KeyData::Counter(self.current_counter);
        self.current_counter += 1;
        result
    }

    #[inline]
    fn new_widget_from_user_key(&mut self, key: Key, props: Props, data: WidgetData) -> NonZeroU32 {
        let key = match key {
            Key::Counter       => self.next_counter_key(),
            Key::U64(value)    => KeyData::U64(value),
            Key::String(value) => KeyData::String(value),
        };
        self.new_widget(key, props, data)
    }

    #[inline]
    fn widget_events(&self, widget: NonZeroU32) -> WidgetEvents {
        let prev_hovered = self.prev_hovered == widget.get();
        let hovered      = self.hovered      == widget.get();
        let prev_active  = self.prev_active  == widget.get();
        let active       = self.active       == widget.get();
        WidgetEvents {
            prev_hovered, hovered,
            prev_active,  active,
        }
    }

    fn render_children(&mut self) {
        let parent = &mut self.widgets[self.current_parent];
        let mut cr = ChildRenderer::new(parent.props.layout.is_flow());

        let mut at = parent.box_data().first_child;
        while let Some(current) = at {
            at = cr.visit(current, self);
        }
        cr.flush(self);

        let box_data = self.widgets[self.current_parent].box_data();
        box_data.first_render_child = cr.first;
        box_data.last_render_child  = cr.last;
    }

    pub fn widget_text(&mut self, key: Key, props: Props, text: String) -> WidgetEvents {
        let data = TextData { text };
        let widget = self.new_widget_from_user_key(key, props, WidgetData::Text(data));
        self.widget_events(widget)
    }

    pub fn widget_box<F: FnOnce(&mut Gui)>(&mut self, key: Key, props: Props, f: F) -> WidgetEvents {
        let widget = self.new_widget_from_user_key(key, props, WidgetData::Box(BoxData::default()));

        // visit children.
        let old_parent  = self.current_parent;
        let old_counter = self.current_counter;
        self.current_parent  = widget.get() as usize;
        self.current_counter = 0;
        f(self);

        self.render_children();

        self.current_parent  = old_parent;
        self.current_counter = old_counter;

        self.widget_events(widget)
    }


    pub fn layout(&mut self) {
        fn intrinsic_pass(this: &mut Gui, widget_index: usize) {
            // reset layout.
            let widget = &mut this.widgets[widget_index];
            widget.pos  = [0.0; 2];
            widget.size = [0.0; 2];
            widget.content_size   = [0.0; 2];
            widget.intrinsic_size = [0.0; 2];

            let content_size = match &widget.data {
                WidgetData::Box(data) => {
                    match widget.props.layout {
                        Layout::None => {
                            let mut at = data.first_render_child;
                            while let Some(current) = at {
                                let current = current.get() as usize;
                                intrinsic_pass(this, current);

                                let child = &mut this.widgets[current];
                                at = child.next_render_sibling;
                            }

                            [0.0; 2]
                        }

                        Layout::Flow => {
                            let mut width  = 0f32;
                            let mut height = 0f32;

                            let mut at = data.first_render_child;
                            while let Some(current) = at {
                                let current = current.get() as usize;
                                intrinsic_pass(this, current);

                                let child = &mut this.widgets[current];
                                width   = width.max(child.intrinsic_size[0]);
                                height += child.intrinsic_size[1];

                                at = child.next_render_sibling;
                            }

                            [width, height]
                        }

                        Layout::Flex(flex) => {
                            let main_axis  = flex.direction.main_axis();
                            let cross_axis = flex.direction.cross_axis();

                            let mut main_size  = 0f32;
                            let mut cross_size = 0f32;

                            let mut at = data.first_render_child;
                            while let Some(current) = at {
                                let current = current.get() as usize;
                                intrinsic_pass(this, current);

                                let child = &mut this.widgets[current];
                                main_size += child.intrinsic_size[main_axis];
                                cross_size = cross_size.max(child.intrinsic_size[cross_axis]);

                                at = child.next_render_sibling;
                            }

                            [[main_size, cross_size][main_axis],
                             [main_size, cross_size][cross_axis]]
                        }
                    }
                }

                WidgetData::TextLayout(data) => {
                    data.layout.size()
                }

                WidgetData::Text(_) | WidgetData::Free(_) => unreachable!()
            };

            let widget = &mut this.widgets[widget_index];
            widget.content_size = content_size;
            widget.intrinsic_size = [
                widget.props.size[0].unwrap_or(content_size[0]),
                widget.props.size[1].unwrap_or(content_size[1])];
        }

        fn layout_pass(this: &mut Gui, widget_index: usize, given_size: [Option<f32>; 2]) {
            let widget = &this.widgets[widget_index];

            let size = match &widget.data {
                WidgetData::Box(data) => {
                    match widget.props.layout {
                        Layout::None => {
                            let size = widget.intrinsic_size;

                            let mut at = data.first_render_child;
                            while let Some(current) = at {
                                let current = current.get() as usize;
                                layout_pass(this, current, [None, None]);

                                let child = &mut this.widgets[current];
                                at = child.next_render_sibling;
                            }

                            size
                        }

                        Layout::Flow => {
                            let width = given_size[0].unwrap_or(widget.intrinsic_size[0]);
                            let height = widget.intrinsic_size[1];

                            let mut cursor = 0f32;

                            let mut at = data.first_render_child;
                            while let Some(current) = at {
                                let current = current.get() as usize;
                                layout_pass(this, current, [Some(width), None]);

                                let child = &mut this.widgets[current];
                                child.pos = [0.0, cursor];
                                cursor += child.size[1];

                                at = child.next_render_sibling;
                            }

                            [width, height.max(cursor)]
                        }

                        Layout::Flex(flex) => {
                            let main_axis  = flex.direction.main_axis();
                            let cross_axis = flex.direction.cross_axis();

                            let main_cont  = widget.content_size[main_axis];

                            let main_intr  = widget.intrinsic_size[main_axis];
                            let cross_intr = widget.intrinsic_size[cross_axis];
                            let main_size  = given_size[main_axis].unwrap_or(main_intr);
                            let cross_size = given_size[cross_axis].unwrap_or(cross_intr);

                            let mut cursor = 0.0;

                            let mut at = data.first_render_child;
                            while let Some(current) = at {
                                let current = current.get() as usize;

                                let child_main = None;
                                // @todo: flex_grow.
                                // let's skip flex grow for now.
                                // but for that, we'll have to know the sum of the grow factors.
                                // prob should compute that in intrinsic_pass.

                                let child_cross = match flex.align {
                                    FlexAlign::Begin |
                                    FlexAlign::End |
                                    FlexAlign::Center => None,

                                    FlexAlign::Stretch => Some(cross_size),
                                };

                                let child_width  = [child_main, child_cross][main_axis];
                                let child_height = [child_main, child_cross][cross_axis];
                                layout_pass(this, current, [child_width, child_height]);

                                let child = &mut this.widgets[current];

                                let child_main  = child.size[main_axis];
                                let child_cross = child.size[cross_axis];

                                let main_pos = match flex.justify {
                                    FlexJustify::Begin  => cursor,
                                    FlexJustify::Center => main_size/2.0 - main_cont/2.0 + cursor,
                                    FlexJustify::End    => main_size - main_cont + cursor,
                                    FlexJustify::SpaceBetween => unimplemented!(),
                                    FlexJustify::SpaceEvenly  => unimplemented!(),
                                };

                                let cross_pos = match flex.align {
                                    FlexAlign::Begin   => 0.0,
                                    FlexAlign::Center  => cross_size/2.0 - child_cross / 2.0,
                                    FlexAlign::End     => cross_size - child_cross,
                                    FlexAlign::Stretch => 0.0,
                                };
                                child.pos[0] = [main_pos, cross_pos][main_axis];
                                child.pos[1] = [main_pos, cross_pos][cross_axis];

                                cursor += child_main;

                                at = child.next_render_sibling;
                            }

                            [[main_size, cross_size][main_axis],
                             [main_size, cross_size][cross_axis]]
                        }
                    }
                }

                WidgetData::TextLayout(data) => {
                    data.layout.size()
                }

                WidgetData::Text(_) | WidgetData::Free(_) => unreachable!()
            };

            let widget = &mut this.widgets[widget_index];
            widget.size = [
                given_size[0].unwrap_or(size[0]),
                given_size[1].unwrap_or(size[1])];
        }

        intrinsic_pass(self, 0);
        layout_pass(self, 0, [Some(self.root_size[0]), Some(self.root_size[1])]);
    }


    pub fn draw(&mut self, r: &mut Renderer) {
        fn rec(this: &mut Gui, widget_index: usize, px: i32, py: i32, r: &mut Renderer) {
            let widget = &this.widgets[widget_index];

            let [x0, y0] = widget.pos;
            let x1 = x0 + widget.size[0];
            let y1 = y0 + widget.size[1];

            let x0 = px + x0 as i32;
            let y0 = py + y0 as i32;
            let x1 = px + x1 as i32;
            let y1 = py + y1 as i32;

            match &widget.data {
                WidgetData::Box(data) => {
                    if widget.props.fill {
                        r.fill_rect_abs(x0, y0, x1, y1, widget.props.fill_color);
                    }

                    let mut at = data.first_render_child;
                    while let Some(current) = at {
                        let current = current.get() as usize;
                        rec(this, current, x0, y0, r);

                        at = this.widgets[current].next_render_sibling;
                    }
                }

                WidgetData::TextLayout(data) => {
                    r.draw_text_layout_abs(x0, y0, &data.layout);
                }

                WidgetData::Text(_) | WidgetData::Free(_) => unreachable!()
            }
        }

        rec(self, 0,  0, 0,  r);
    }


    pub fn update<F: FnOnce(&mut Gui) -> bool>(&mut self, root_props: Props, f: F) -> bool {
        self.begin(root_props);
        let result = f(self);
        self.end();
        self.layout();
        result
    }


    pub fn root_size(&mut self, root_size: [f32; 2]) -> bool {
        if self.root_size == root_size {
            return false;
        }
        self.root_size = root_size;
        return true;
    }

    pub fn mouse_move(&mut self, mx: f32, my: f32) -> bool {
        if mx == self.mouse_pos[0] && my == self.mouse_pos[1] {
            return false;
        }
        self.mouse_pos = [mx, my];

        let hit = self.hit_test_filtered(mx, my, |hit| self.widgets[hit].props.pointer_events);

        let prev_hovered = self.hovered;

        if let Some(hit) = hit {
            self.hovered = hit.0;
        }
        else {
            self.hovered = 0;
        }

        return self.hovered != prev_hovered;
    }

    pub fn mouse_down(&mut self, is_down: bool) -> bool {
        if is_down == self.mouse_down {
            return false;
        }
        self.mouse_down = is_down;

        let prev_active = self.active;

        if is_down {
            self.active = self.hovered;
        }
        else {
            self.active = 0;
        }

        return self.active != prev_active;
    }
}


struct ChildRenderer {
    merge_text: bool,
    first: OptWidgetId,
    last:  OptWidgetId,
    counter: u32,
    text_layout: Option<TextLayout>,
}

impl ChildRenderer {
    fn new(merge_text: bool) -> ChildRenderer {
        ChildRenderer { merge_text, first: None, last: None, counter: 0, text_layout: None }
    }

    fn append(&mut self, widget: NonZeroU32, gui: &mut Gui) {
        let prev_render_sibling = self.last;
        if let Some(last) = prev_render_sibling {
            let l = &mut gui.widgets[last.get() as usize];
            l.next_render_sibling = Some(widget);
        }
        else {
            assert!(self.first.is_none());
            self.first = Some(widget);
        }

        let w = &mut gui.widgets[widget.get() as usize];
        w.prev_render_sibling = prev_render_sibling;
        w.next_render_sibling = None;

        self.last = Some(widget);
    }

    fn flush(&mut self, gui: &mut Gui) {
        if let Some(layout) = self.text_layout.take() {
            let key = KeyData::TextLayout(self.counter);
            self.counter += 1;

            let data = TextLayoutData { layout };

            let widget = gui.alloc_widget(key, Props::new(), WidgetData::TextLayout(data));
            self.append(widget, gui);
        }
    }

    fn visit(&mut self, child: NonZeroU32, gui: &mut Gui) -> OptWidgetId {
        let widget = &gui.widgets[child.get() as usize];
        let next = widget.next_sibling;

        match &widget.data {
            WidgetData::Box(_) => {
                self.flush(gui);
                self.append(child, gui);
            }

            WidgetData::Text(text) => {
                // kinda wanna flush here,
                // but can't borrow gui as mutable.
                // oh well, just don't break it, ok?
                if self.text_layout.is_none() {
                    self.text_layout = Some(TextLayout::new(&gui.fonts));
                }
                else { debug_assert!(self.merge_text) }

                let layout = self.text_layout.as_mut().unwrap();
                layout.append(
                    &text.text,
                    widget.props.font_face,
                    widget.props.font_size,
                    widget.props.text_color,
                    child.get());

                if !self.merge_text {
                    self.flush(gui);
                }
            }

            WidgetData::TextLayout(_) | WidgetData::Free(_) => unreachable!()
        }

        next
    }
}

