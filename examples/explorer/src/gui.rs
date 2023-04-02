use core::num::NonZeroU32;
use crate::renderer::*;


#[allow(dead_code)] // @temp
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Key {
    Counter,
    U64     (u64),
    String  (String),
}

impl Default for Key { #[inline(always)] fn default() -> Self { Key::Counter } }


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


#[allow(dead_code)] // @temp
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Overflow {
    Visible,
    Clip,
    Scroll,
    AutoScroll,
}

impl Default for Overflow { #[inline(always)] fn default() -> Self { Overflow::Visible } }


#[derive(Clone, Debug)]
pub struct Props {
    pub pos:  [Option<f32>; 2],
    pub size: [Option<f32>; 2],

    pub layout: Layout,
    pub flex_grow: f32,

    // left/right, top/bottom.
    pub margin:  [[f32; 2]; 2],
    pub padding: [[f32; 2]; 2],

    pub overflow: [Overflow; 2],

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
            pos:  [None; 2],
            size: [None; 2],

            layout: Layout::default(),
            flex_grow: 0.,
            margin:  [[0.0; 2]; 2],
            padding: [[0.0; 2]; 2],

            overflow: [Overflow::default(); 2],

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
    TextLayout (u32),
    Scrollbar  (ScrollbarPart),
}


#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ScrollbarPart {
    X,
    Y,
    Corner,
}


#[derive(Clone, Copy, Debug)]
pub struct ScrollbarInfo {
    parent: u32,
    pub parent_size: [f32; 2],
    pub content_max: [f32; 2],
    pub scroll_pos:  [f32; 2],
    pub scrollbar_sizes: [f32; 2],
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
    content_min: [f32; 2],
    content_max: [f32; 2],
    hit_min: [f32; 2],
    hit_max: [f32; 2],

    // scroll stuff.
    clip:            [bool; 2],
    scroll_pos:      [f32; 2],
    has_scrollbars:  [bool; 2],
    scrollbar_sizes: [f32; 2],
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
    scrollbar_parts:    [OptWidgetId; 3],
}

impl BoxData {
    #[inline(always)]
    fn default() -> BoxData {
        BoxData {
            first_child: None, last_child: None,
            first_render_child: None, last_render_child: None,
            scrollbar_parts: [None; 3],
        }
    }
}


struct TextLayoutData {
    layout: TextLayout,
    first_render_child: OptWidgetId,
    last_render_child:  OptWidgetId,
}

struct TextData {
    text: String,
    layout_begin: u32,
    layout_end:   u32,
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



#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MouseButton {
    Left,
    Middle,
    Right,
}



#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct WidgetId(u32);


#[derive(Clone, Copy, Debug)]
pub struct WidgetEvents {
    widget: u32,
    pub local_offset:    [f32; 2],

    pub size:        [f32; 2],
    pub content_min: [f32; 2],
    pub content_max: [f32; 2],
    pub scroll_pos:  [f32; 2],

    pub prev_mouse_pos:  [f32; 2],
    pub mouse_pos:       [f32; 2],
    pub prev_mouse_down: [bool; 3],
    pub mouse_down:      [bool; 3],

    pub prev_hovered:   bool,
    pub hovered:        bool,
    pub prev_active:    bool,
    pub active:         bool,
}

impl WidgetEvents {
    #[allow(dead_code)] // @temp
    #[inline(always)]
    pub fn hover_begin(&self) -> bool {
        self.hovered && !self.prev_hovered
    }

    #[inline(always)]
    pub fn hover_changed(&self) -> bool {
        self.hovered != self.prev_hovered
    }

    #[inline(always)]
    pub fn active_begin(&self) -> bool {
        self.active && !self.prev_active
    }

    #[inline(always)]
    pub fn active_changed(&self) -> bool {
        self.active != self.prev_active
    }

    #[inline(always)]
    pub fn clicked(&self) -> bool {
        self.prev_active && !self.active && self.hovered
    }

    #[inline(always)]
    pub fn mouse_moved(&self) -> bool {
        let [x0, y0] = self.prev_mouse_pos;
        let [x1, y1] = self.mouse_pos;
        x1 != x0 || y1 != y0
    }

    #[allow(dead_code)] // @temp
    #[inline(always)]
    pub fn mouse_delta(&self) -> Option<(f32, f32)> {
        let [x0, y0] = self.prev_mouse_pos;
        let [x1, y1] = self.mouse_pos;
        (x1 != x0 || y1 != y0).then_some((x1 - x0, y1 - y0))
    }

    #[allow(dead_code)] // @temp
    #[inline(always)]
    pub fn mouse_is_down(&self, button: MouseButton) -> bool {
        self.mouse_down[button as usize]
    }

    #[inline(always)]
    pub fn mouse_went_down(&self, button: MouseButton) -> bool {
        self.mouse_down[button as usize] && !self.prev_mouse_down[button as usize]
    }

    #[allow(dead_code)] // @temp
    #[inline(always)]
    pub fn mouse_went_up(&self, button: MouseButton) -> bool {
        !self.mouse_down[button as usize] && self.prev_mouse_down[button as usize]
    }

    #[inline(always)]
    pub fn local_mouse_pos(&self) -> [f32; 2] {
        [self.mouse_pos[0] - self.local_offset[0],
         self.mouse_pos[1] - self.local_offset[1]]
    }
}


pub struct Gui {
    gen:        u64,
    widgets:    Vec<Widget>,
    first_free: OptWidgetId,
    hash:       Vec<OptWidgetId>,

    current_parent:  usize,
    current_counter: u32,
    current_offset:  [f32; 2],

    fonts: FontCtx,

    needs_update: bool,
    needs_render: bool,

    root_size:  [f32; 2],

    prev_mouse_pos:  [f32; 2],
    mouse_pos:       [f32; 2],
    prev_mouse_down: [bool; 3],
    mouse_down:      [bool; 3],

    prev_hovered: u32,
    hovered:      u32,
    prev_active:  u32,
    active:       u32,

    prev_mouse_capture: Option<(MouseButton, u32)>,
    mouse_capture:      Option<(MouseButton, u32)>,
    mouse_capture_pos:  [f32; 2], // widget local position
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
            content_min: [0.0; 2],
            content_max: [0.0; 2],
            hit_min: [0.0; 2],
            hit_max: [0.0; 2],

            clip:            [false; 2],
            scroll_pos:      [0.0; 2],
            has_scrollbars:  [false; 2],
            scrollbar_sizes: [0.0; 2],
        };

        Gui {
            gen:        1,
            widgets:    vec![root],
            first_free: None,
            hash:       vec![None; 16*1024], // @temp

            current_parent:  usize::MAX,
            current_counter: 0,
            current_offset:  [0.0; 2],

            fonts: fonts.clone(),

            needs_update: false,
            needs_render: false,

            root_size:  [0.0; 2],

            prev_mouse_pos:  [0.0; 2],
            mouse_pos:       [0.0; 2],
            prev_mouse_down: [false; 3],
            mouse_down:      [false; 3],

            prev_hovered: 0,
            hovered:      0,
            prev_active:  0,
            active:       0,

            prev_mouse_capture: None,
            mouse_capture:      None,
            mouse_capture_pos:  [0.0; 2],
        }
    }


    pub fn measure_string(&self, string: &str, face: FaceId, size: f32) -> [f32; 2] {
        let mut layout = TextLayout::new(&self.fonts);
        layout.append(string, face, size, 0, 0);
        layout.size()
    }


    fn hit_test_filtered<F: FnMut(usize) -> bool>(&self, x: f32, y: f32, mut f: F) -> Option<WidgetId> {
        fn rec<F: FnMut(usize) -> bool>(this: &Gui, widget_index: usize, x: f32, y: f32, f: &mut F) -> Option<WidgetId> {
            let widget = &this.widgets[widget_index];

            let x = x - widget.pos[0];
            let y = y - widget.pos[1];

            let hit_self_x = x >= 0.0 && x < widget.size[0];
            let hit_self_y = y >= 0.0 && y < widget.size[1];
            let hit_self = hit_self_x && hit_self_y;

            let cx = x + widget.scroll_pos[0];
            let cy = y + widget.scroll_pos[1];

            let hit_clip_x = !widget.clip[0] || hit_self_x;
            let hit_clip_y = !widget.clip[1] || hit_self_y;
            let hit_clip = hit_clip_x && hit_clip_y;

            let hit_content_x = hit_clip && cx >= widget.hit_min[0] && cx < widget.hit_max[0];
            let hit_content_y = hit_clip && cy >= widget.hit_min[1] && cy < widget.hit_max[1];
            let hit_content = hit_content_x && hit_content_y;

            if !hit_content {
                let return_self = hit_self && f(widget_index);
                return return_self.then_some(WidgetId(widget_index as u32));
            }

            let result = match &widget.data {
                WidgetData::Box(data) => {
                    let mut at = data.last_render_child;
                    while let Some(current) = at {
                        let current = current.get() as usize;
                        let result = rec(this, current, cx, cy, f);
                        if result.is_some() {
                            return result;
                        }

                        at = this.widgets[current].prev_render_sibling;
                    }

                    hit_self.then_some(WidgetId(widget_index as u32))
                }

                WidgetData::TextLayout(data) => {
                    let hit = data.layout.hit_test_pos(x, y);
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
        self.current_offset  = [0.0; 2];

        self.needs_update = false;
        self.needs_render = false;

        self.widgets[0].begin(self.gen, root_props, WidgetData::Box(BoxData::default()));
    }

    pub fn end(&mut self) {
        assert_eq!(self.current_parent, 0);
        self.render_children();
        self.current_parent = usize::MAX;

        self.prev_mouse_pos  = self.mouse_pos;
        self.prev_mouse_down = self.mouse_down;
        self.prev_hovered = self.hovered;
        self.prev_active  = self.active;
        self.prev_mouse_capture = self.mouse_capture;

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
                widget.prev_sibling = None;
                widget.next_sibling = None;
                widget.prev_render_sibling = None;
                widget.next_render_sibling = None;

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

        // remove freed widgets from event data.
        {
            if self.widgets[self.prev_hovered as usize].data.is_free() { self.prev_hovered = 0 }
            if self.widgets[self.hovered      as usize].data.is_free() { self.hovered      = 0 }
            if self.widgets[self.prev_active  as usize].data.is_free() { self.prev_active  = 0 }
            if self.widgets[self.active       as usize].data.is_free() { self.active       = 0 }

            if let Some((_, widget)) = self.prev_mouse_capture {
                if self.widgets[widget as usize].data.is_free() {
                    self.prev_mouse_capture = None;
                }
            }
            if let Some((_, widget)) = self.mouse_capture {
                if self.widgets[widget as usize].data.is_free() {
                    self.mouse_capture = None;
                }
            }
        }

        #[cfg(debug_assertions)]
        self.validate();
    }


    #[allow(dead_code)]
    fn validate(&self) {
        fn validate_children(gui: &Gui, index: usize, visited: &mut [bool]) {
            assert!(visited[index] == false);
            visited[index] = true;

            let widget = &gui.widgets[index];
            match &widget.data {
                WidgetData::Box(data) => {
                    let mut previous = None;
                    let mut at = data.first_child;
                    while let Some(current) = at {
                        let child = current.get() as usize;
                        let widget = &gui.widgets[child];
                        assert_eq!(widget.prev_sibling, previous);
                        assert_eq!(widget.parent as usize, index);

                        validate_children(gui, child, visited);

                        previous = at;
                        at = widget.next_sibling;
                    }

                    if let Some(last) = data.last_child {
                        assert_eq!(previous, Some(last));
                    }
                    else {
                        assert_eq!(data.first_child, None);
                    }

                    for part in data.scrollbar_parts {
                        if let Some(part) = part {
                            validate_children(gui, part.get() as usize, visited);
                        }
                    }
                }

                WidgetData::TextLayout(_) => {}

                WidgetData::Text(_) => {}

                WidgetData::Free(_) => unreachable!(),
            }
        }

        // validate children.
        {
            let mut visited = vec![false; self.widgets.len()];
            validate_children(self, 0, &mut visited);

            for (index, widget) in self.widgets.iter().enumerate() {
                match &widget.data {
                    WidgetData::Box(_) => assert!(visited[index]),

                    WidgetData::TextLayout(_) => assert!(visited[index] == false),

                    WidgetData::Text(_) => assert!(visited[index]),

                    WidgetData::Free(_) => {
                        assert!(visited[index] == false);
                        assert_eq!(widget.hash_prev, None);
                        assert_eq!(widget.hash_next, None);
                        assert_eq!(widget.prev_sibling, None);
                        assert_eq!(widget.next_sibling, None);
                        assert_eq!(widget.prev_render_sibling, None);
                        assert_eq!(widget.next_render_sibling, None);
                    }
                }
            }
        }


        fn validate_render_children(gui: &Gui, index: usize, visited: &mut [bool]) {
            assert!(visited[index] == false);
            visited[index] = true;

            let widget = &gui.widgets[index];
            match widget.data {
                WidgetData::Box(BoxData { first_render_child, last_render_child, .. }) |
                WidgetData::TextLayout(TextLayoutData { layout: _, first_render_child, last_render_child }) => {
                    let mut previous = None;
                    let mut at = first_render_child;
                    while let Some(current) = at {
                        let child = current.get() as usize;
                        let widget = &gui.widgets[child];
                        assert_eq!(widget.prev_render_sibling, previous);

                        validate_render_children(gui, child, visited);

                        previous = at;
                        at = widget.next_render_sibling;
                    }

                    if let Some(last) = last_render_child {
                        assert_eq!(previous, Some(last));
                    }
                    else {
                        assert_eq!(first_render_child, None);
                    }
                }

                WidgetData::Text(_) => (),

                WidgetData::Free(_) => unreachable!(),
            }
        }

        // validate render children.
        {
            let mut visited = vec![false; self.widgets.len()];
            validate_render_children(self, 0, &mut visited);

            for (index, widget) in self.widgets.iter().enumerate() {
                match &widget.data {
                    WidgetData::Box(_) |
                    WidgetData::TextLayout(_) |
                    WidgetData::Text(_) => assert!(visited[index]),

                    WidgetData::Free(_) => assert!(visited[index] == false),
                }
            }
        }

        // validate free list.
        {
            let mut at = self.first_free;
            while let Some(current) = at {
                let WidgetData::Free(next) = self.widgets[current.get() as usize].data else { unreachable!() };
                at = next;
            }
        }

        // validate hash map.
        {
            let mut visited = vec![false; self.widgets.len()];
            visited[0] = true;

            for i in 0..self.hash.len() {
                let mut previous = None;
                let mut at = self.hash[i];
                while let Some(current) = at {
                    let index = current.get() as usize;
                    assert!(visited[index] == false);
                    visited[index] = true;

                    let widget = &self.widgets[index];
                    assert_eq!(widget.hash_prev, previous);

                    let hash = Self::hash((widget.parent, &widget.key));
                    let slot = hash as usize & (self.hash.len() - 1);
                    assert_eq!(slot, i);

                    previous = at;
                    at = widget.hash_next;
                }
            }

            for (index, widget) in self.widgets.iter().enumerate() {
                match &widget.data {
                    WidgetData::Box(_) |
                    WidgetData::TextLayout(_) |
                    WidgetData::Text(_) => assert!(visited[index]),

                    WidgetData::Free(_) => assert!(visited[index] == false),
                }
            }
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
                    content_min: [0.0; 2],
                    content_max: [0.0; 2],
                    hit_min: [0.0; 2],
                    hit_max: [0.0; 2],

                    clip:            [false; 2],
                    scroll_pos:      [0.0; 2],
                    has_scrollbars:  [false; 2],
                    scrollbar_sizes: [0.0; 2],
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

        let mouse_events =
            if let Some((_, capture_widget)) = self.prev_mouse_capture {
                widget.get() == capture_widget
            }
            else { hovered && prev_hovered };

        let (prev_mouse_pos, prev_mouse_down) =
            if mouse_events { (self.prev_mouse_pos, self.prev_mouse_down) }
            else            { (self.mouse_pos,      self.mouse_down)      };

        let w = &self.widgets[widget.get() as usize];
        let local_offset = [
            self.current_offset[0] + w.pos[0],
            self.current_offset[1] + w.pos[1],
        ];

        WidgetEvents {
            widget: widget.get(),
            local_offset,
            size:        w.size,
            content_min: w.content_min,
            content_max: w.content_max,
            scroll_pos:  w.scroll_pos,
            prev_mouse_pos,  mouse_pos:  self.mouse_pos,
            prev_mouse_down, mouse_down: self.mouse_down,
            prev_hovered, hovered,
            prev_active,  active,
        }
    }

    fn render_children(&mut self) {
        let parent = &mut self.widgets[self.current_parent];
        let mut cr = ChildRenderer::new(parent.props.layout.is_flow());

        let box_data = parent.box_data();
        let scrollbar_parts = box_data.scrollbar_parts;

        let mut at = box_data.first_child;
        while let Some(current) = at {
            at = cr.visit(current, self);
        }

        for part in scrollbar_parts {
            if let Some(part) = part {
                cr.visit(part, self);
            }
        }

        cr.flush(self);

        let box_data = self.widgets[self.current_parent].box_data();
        box_data.first_render_child = cr.first;
        box_data.last_render_child  = cr.last;
    }

    pub fn widget_text(&mut self, key: Key, props: Props, text: String) -> WidgetEvents {
        let data = TextData { text, layout_begin: u32::MAX, layout_end: u32::MAX };
        let widget = self.new_widget_from_user_key(key, props, WidgetData::Text(data));
        self.widget_events(widget)
    }

    fn widget_box_children<F: FnOnce(&mut Gui)>(&mut self, widget: NonZeroU32, f: F) -> WidgetEvents {
        let w = &self.widgets[widget.get() as usize];
        let pos    = w.pos;
        let scroll = w.scroll_pos;

        // visit children.
        let old_parent  = self.current_parent;
        let old_counter = self.current_counter;
        let old_offset  = self.current_offset;
        self.current_parent  = widget.get() as usize;
        self.current_counter = 0;
        self.current_offset[0] += pos[0] - scroll[0];
        self.current_offset[1] += pos[1] - scroll[1];

        f(self);

        self.render_children();

        self.current_parent  = old_parent;
        self.current_counter = old_counter;
        self.current_offset  = old_offset;

        self.widget_events(widget)
    }

    pub fn widget_box<F: FnOnce(&mut Gui)>(&mut self, key: Key, props: Props, f: F) -> WidgetEvents {
        let widget = self.new_widget_from_user_key(key, props, WidgetData::Box(BoxData::default()));
        self.widget_box_children(widget, f)
    }

    pub fn widget_scrollbar_part<F: FnOnce(&mut Gui, ScrollbarInfo)>(&mut self, part: ScrollbarPart, props: Props, f: F) -> WidgetEvents {
        let widget = self.alloc_widget(KeyData::Scrollbar(part), props, WidgetData::Box(BoxData::default()));

        let parent = &mut self.widgets[self.current_parent];
        let WidgetData::Box(data) = &mut parent.data else { unreachable!() };

        data.scrollbar_parts[part as usize] = Some(widget);

        let info = ScrollbarInfo { 
            parent: self.current_parent as u32,
            parent_size: parent.size,
            content_max: parent.content_max, 
            scroll_pos:  parent.scroll_pos,
            scrollbar_sizes: [
                if parent.has_scrollbars[0] { parent.scrollbar_sizes[0] } else { 0.0 },
                if parent.has_scrollbars[1] { parent.scrollbar_sizes[1] } else { 0.0 },
            ],
        };

        self.widget_box_children(widget, |gui| f(gui, info))
    }


    pub fn layout(&mut self) {
        fn intrinsic_pass(this: &mut Gui, widget_index: usize, allow_scrollbar: bool) {
            // reset layout.
            let widget = &mut this.widgets[widget_index];
            widget.content_size   = [0.0; 2];
            widget.intrinsic_size = [0.0; 2];

            if !allow_scrollbar && matches!(widget.key, KeyData::Scrollbar(_)) {
                return;
            }

            let content_size = match &widget.data {
                WidgetData::Box(data) => {
                    match widget.props.layout {
                        Layout::None => {
                            let mut at = data.first_render_child;
                            while let Some(current) = at {
                                let current = current.get() as usize;
                                intrinsic_pass(this, current, false);

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
                                intrinsic_pass(this, current, false);

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
                                intrinsic_pass(this, current, false);

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

            let widget = &this.widgets[widget_index];

            // scrollbar parts.
            //  the sizes are a bit unintuitive:
            //  scrollbar_sizes[0] is "the size" of the `X` scrollbar,
            //  but that's a "height".
            let mut scrollbar_sizes = [0.0; 2];
            if let WidgetData::Box(data) = widget.data {
                if let Some(part) = data.scrollbar_parts[ScrollbarPart::X as usize] {
                    let part = part.get() as usize;
                    intrinsic_pass(this, part, true);
                    scrollbar_sizes[0] = this.widgets[part].intrinsic_size[1];
                }
                if let Some(part) = data.scrollbar_parts[ScrollbarPart::Y as usize] {
                    let part = part.get() as usize;
                    intrinsic_pass(this, part, true);
                    scrollbar_sizes[1] = this.widgets[part].intrinsic_size[0];
                }
                if let Some(part) = data.scrollbar_parts[ScrollbarPart::Corner as usize] {
                    intrinsic_pass(this, part.get() as usize, true);
                }
            }


            let widget = &mut this.widgets[widget_index];

            let mgn = widget.props.margin;
            let pad = widget.props.padding;
            let intr_size = [
                content_size[0] + mgn[0][0]+mgn[0][1] + pad[0][0]+pad[0][1],
                content_size[1] + mgn[1][0]+mgn[1][1] + pad[1][0]+pad[1][1],
            ];

            widget.content_size = content_size;
            widget.intrinsic_size = [
                widget.props.size[0].unwrap_or(intr_size[0]),
                widget.props.size[1].unwrap_or(intr_size[1])];

            widget.scrollbar_sizes = scrollbar_sizes;
        }

        fn layout_pass(this: &mut Gui, widget_index: usize, given_size: [Option<f32>; 2], allow_scrollbar: bool) {
            let widget = &mut this.widgets[widget_index];
            let old_size = widget.size;
            let old_cmax = widget.content_max;
            widget.pos  = [0.0; 2];
            widget.size = [0.0; 2];
            widget.content_min = [0.0; 2];
            widget.content_max = [0.0; 2];
            widget.hit_min = [0.0; 2];
            widget.hit_max = [0.0; 2];

            if !allow_scrollbar && matches!(widget.key, KeyData::Scrollbar(_)) {
                return;
            }


            let mut scrollbar_sizes;

            let mut has_scrollbars = [
                widget.props.overflow[0] == Overflow::Scroll,
                widget.props.overflow[1] == Overflow::Scroll,
            ];

            let given_size = [
                given_size[0].or(widget.props.size[0]),
                given_size[1].or(widget.props.size[1]),
            ];


            loop {
                let widget = &this.widgets[widget_index];

                let mut cmin = [0f32; 2];
                let mut cmax = [0f32; 2];

                #[inline]
                fn add_child(child: &Widget, cmin: &mut [f32; 2], cmax: &mut [f32; 2]) {
                    cmin[0] = cmin[0].min(child.pos[0] + child.content_min[0]);
                    cmin[1] = cmin[1].min(child.pos[1] + child.content_min[1]);
                    cmax[0] = cmax[0].max(child.pos[0] + child.content_max[0]).max(child.pos[0] + child.size[0]);
                    cmax[1] = cmax[1].max(child.pos[1] + child.content_max[1]).max(child.pos[1] + child.size[1]);
                }

                let mgn = widget.props.margin;
                let pad = widget.props.padding;

                let space_x0 = mgn[0][0] + pad[0][0];
                let space_y0 = mgn[1][0] + pad[1][0];
                let space_x1 = mgn[0][1] + pad[0][1];
                let space_y1 = mgn[1][1] + pad[1][1];
                let space_x  = space_x0 + space_x1;
                let space_y  = space_y0 + space_y1;


                // again (see above): scrollbar_sizes[0] is a height.
                scrollbar_sizes = [
                    if has_scrollbars[0] { widget.scrollbar_sizes[0] } else { 0.0 },
                    if has_scrollbars[1] { widget.scrollbar_sizes[1] } else { 0.0 },
                ];

                let inner_size = [
                    given_size[0].map(|size| (size - scrollbar_sizes[1]).max(0.0)),
                    given_size[1].map(|size| (size - scrollbar_sizes[0]).max(0.0)),
                ];

                let size = match &widget.data {
                    WidgetData::Box(data) => {
                        match widget.props.layout {
                            Layout::None => {
                                let size = widget.intrinsic_size;

                                let mut at = data.first_render_child;
                                while let Some(current) = at {
                                    let current = current.get() as usize;
                                    layout_pass(this, current, [None, None], false);

                                    let child = &mut this.widgets[current];
                                    child.pos = [
                                        space_x0 + child.props.pos[0].unwrap_or(0.0),
                                        space_y0 + child.props.pos[1].unwrap_or(0.0)];

                                    add_child(child, &mut cmin, &mut cmax);

                                    at = child.next_render_sibling;
                                }

                                size
                            }

                            Layout::Flow => {
                                let width = inner_size[0].unwrap_or(widget.intrinsic_size[0]);
                                let height = widget.intrinsic_size[1];

                                let mut cursor = space_y0;

                                let mut at = data.first_render_child;
                                while let Some(current) = at {
                                    let current = current.get() as usize;
                                    layout_pass(this, current, [Some(width - space_x), None], false);

                                    let child = &mut this.widgets[current];
                                    child.pos = [space_x0, cursor];
                                    cursor += child.size[1];

                                    add_child(child, &mut cmin, &mut cmax);

                                    at = child.next_render_sibling;
                                }
                                cursor += space_y1;

                                [width, height.max(cursor)]
                            }

                            Layout::Flex(flex) => {
                                let main_axis  = flex.direction.main_axis();
                                let cross_axis = flex.direction.cross_axis();

                                let main_cont  = widget.content_size[main_axis];

                                let main_space  = [space_x, space_y][main_axis];
                                let cross_space = [space_x, space_y][cross_axis];

                                let main_space_0  = [space_x0, space_y0][main_axis];
                                let cross_space_0 = [space_x1, space_y1][main_axis];

                                let own_main_intr  = widget.intrinsic_size[main_axis];
                                let own_cross_intr = widget.intrinsic_size[cross_axis];
                                let own_main_size  = inner_size[main_axis].unwrap_or(own_main_intr);
                                let own_cross_size = inner_size[cross_axis].unwrap_or(own_cross_intr);

                                let main_size  = own_main_size  - main_space;
                                let cross_size = own_cross_size - cross_space;


                                let mut cursor = main_space_0;

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
                                    layout_pass(this, current, [child_width, child_height], false);

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

                                    let cross_pos = cross_space_0 + match flex.align {
                                        FlexAlign::Begin   => 0.0,
                                        FlexAlign::Center  => cross_size/2.0 - child_cross / 2.0,
                                        FlexAlign::End     => cross_size - child_cross,
                                        FlexAlign::Stretch => 0.0,
                                    };
                                    child.pos[0] = [main_pos, cross_pos][main_axis];
                                    child.pos[1] = [main_pos, cross_pos][cross_axis];

                                    cursor += child_main;

                                    add_child(child, &mut cmin, &mut cmax);

                                    at = child.next_render_sibling;
                                }

                                [[own_main_size, own_cross_size][main_axis],
                                 [own_main_size, own_cross_size][cross_axis]]
                            }
                        }
                    }

                    WidgetData::TextLayout(data) => {
                        let size = data.layout.size();
                        cmax = size;
                        size
                    }

                    WidgetData::Text(_) | WidgetData::Free(_) => unreachable!()
                };

                let size =
                    [given_size[0].unwrap_or(size[0] + scrollbar_sizes[1]),
                     given_size[1].unwrap_or(size[1] + scrollbar_sizes[0])];

                let widget = &mut this.widgets[widget_index];

                // additional scrollbars.
                if widget.props.overflow[0] == Overflow::AutoScroll {
                    if !has_scrollbars[0] && cmax[0] > size[0] - scrollbar_sizes[1] {
                        has_scrollbars[0] = true;
                        continue;
                    }
                }
                if widget.props.overflow[1] == Overflow::AutoScroll {
                    if !has_scrollbars[1] && cmax[1] > size[1] - scrollbar_sizes[0] {
                        has_scrollbars[1] = true;
                        continue;
                    }
                }

                if has_scrollbars != widget.has_scrollbars {
                    this.needs_update = true;
                }

                // make sure content includes self.
                // otherwise hit testing doesn't work
                // for empty box widgets (eg: blank button).
                let mut hmin = cmin;
                let mut hmax = [ cmax[0].max(size[0]), cmax[1].max(size[1]) ];


                // scrollbar sizes & positions.
                if has_scrollbars[0] || has_scrollbars[1] {
                    let WidgetData::Box(data) = widget.data else { unreachable!() };

                    let x0 = widget.scroll_pos[0];
                    let y0 = widget.scroll_pos[1];

                    if has_scrollbars[0] {
                        if let Some(x_part) = data.scrollbar_parts[ScrollbarPart::X as usize] {
                            let x_part = x_part.get() as usize;

                            let x_size = [
                                Some(size[0] - scrollbar_sizes[1]),
                                Some(scrollbar_sizes[0]),
                            ];
                            layout_pass(this, x_part, x_size, true);

                            let x_part = &mut this.widgets[x_part];
                            x_part.pos = [ x0, y0 + size[1] - scrollbar_sizes[0] ];

                            add_child(x_part, &mut hmin, &mut hmax);
                        }
                    }

                    if has_scrollbars[1] {
                        if let Some(y_part) = data.scrollbar_parts[ScrollbarPart::Y as usize] {
                            let y_part = y_part.get() as usize;

                            let y_size = [
                                Some(scrollbar_sizes[1]),
                                Some(size[1] - scrollbar_sizes[0]),
                            ];
                            layout_pass(this, y_part, y_size, true);

                            let y_part = &mut this.widgets[y_part];
                            y_part.pos = [ x0 + size[0] - scrollbar_sizes[1], y0 ];

                            add_child(y_part, &mut hmin, &mut hmax);
                        }
                    }

                    if has_scrollbars[0] && has_scrollbars[1] {
                        if let Some(corner) = data.scrollbar_parts[ScrollbarPart::Corner as usize] {
                            let corner = &mut this.widgets[corner.get() as usize];
                            corner.pos  = [ x0 + size[0] - scrollbar_sizes[1], y0 + size[1] - scrollbar_sizes[0] ];
                            corner.size = [ scrollbar_sizes[1], scrollbar_sizes[0] ];

                            // don't need to add corner.
                            // covered by other parts.
                        }
                    }
                }


                debug_assert!(size[0] >= 0.0);
                debug_assert!(size[1] >= 0.0);
                debug_assert!(cmin[0] <= 0.0);
                debug_assert!(cmin[1] <= 0.0);
                debug_assert!(cmax[0] >= 0.0);
                debug_assert!(cmax[1] >= 0.0);
                debug_assert!(hmin[0] <= 0.0);
                debug_assert!(hmin[1] <= 0.0);
                debug_assert!(hmax[0] >= 0.0);
                debug_assert!(hmax[1] >= 0.0);


                let widget = &mut this.widgets[widget_index];

                if !this.needs_update {
                    if has_scrollbars[0] || has_scrollbars[1] {
                        if size != old_size || cmax != old_cmax {
                            this.needs_update = true;
                        }
                    }
                }

                widget.size        = size;
                widget.content_min = cmin;
                widget.content_max = cmax;
                widget.hit_min = hmin;
                widget.hit_max = hmax;
                widget.clip = [
                    widget.props.overflow[0] != Overflow::Visible,
                    widget.props.overflow[1] != Overflow::Visible,
                ];
                widget.has_scrollbars = has_scrollbars;

                break;
            }
        }

        intrinsic_pass(self, 0, false);
        layout_pass(self, 0, [Some(self.root_size[0]), Some(self.root_size[1])], false);
    }


    pub fn draw(&mut self, r: &mut Renderer) {
        fn rec(this: &mut Gui, widget_index: usize, px: i32, py: i32, r: &mut Renderer) {
            let widget = &this.widgets[widget_index];

            let [x0, y0] = widget.pos;
            let x1 = x0 + widget.size[0];
            let y1 = y0 + widget.size[1];

            let global_x0 = px + x0 as i32;
            let global_y0 = py + y0 as i32;

            match &widget.data {
                WidgetData::Box(data) => {
                    if widget.props.fill {
                        let mgn = widget.props.margin;
                        r.fill_rect_abs(
                            px + (x0 + mgn[0][0]) as i32,
                            py + (y0 + mgn[1][0]) as i32,
                            px + (x1 - mgn[0][1]) as i32,
                            py + (y1 - mgn[1][1]) as i32,
                            widget.props.fill_color);
                    }

                    let has_clip = widget.clip[0] || widget.clip[1];
                    if has_clip {
                        let global_x1 = px + x1 as i32;
                        let global_y1 = py + y1 as i32;

                        let cx = widget.clip[0];
                        let cy = widget.clip[1];
                        r.push_clip_rect(
                            if cx { global_x0 } else { i32::MIN },
                            if cy { global_y0 } else { i32::MIN },
                            if cx { global_x1 } else { i32::MAX },
                            if cy { global_y1 } else { i32::MAX });
                    }

                    let content_x0 = global_x0 - widget.scroll_pos[0] as i32;
                    let content_y0 = global_y0 - widget.scroll_pos[1] as i32;

                    let mut at = data.first_render_child;
                    while let Some(current) = at {
                        let current = current.get() as usize;
                        rec(this, current, content_x0, content_y0, r);

                        at = this.widgets[current].next_render_sibling;
                    }

                    if has_clip {
                        r.pop_clip_rect();
                    }
                }

                WidgetData::TextLayout(data) => {
                    // text fill.
                    let mut at = data.first_render_child;
                    while let Some(current) = at {
                        let widget = &this.widgets[current.get() as usize];

                        if let WidgetData::Text(text) = &widget.data {
                            if widget.props.fill {
                                data.layout.hit_test_text_ranges(text.layout_begin, text.layout_end, |range| {
                                    let x0 = global_x0 + range.x0 as i32;
                                    let y0 = global_y0 + range.y  as i32;
                                    let x1 = global_x0 + range.x1 as i32;
                                    let y1 = global_y0 + (range.y + range.line_height) as i32;
                                    r.fill_rect_abs(x0, y0, x1, y1, widget.props.fill_color);
                                });
                            }
                        }

                        at = widget.next_render_sibling;
                    }

                    r.draw_text_layout_abs(global_x0, global_y0, &data.layout);
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
        result | self.needs_update
    }


    pub fn root_size(&mut self, root_size: [f32; 2]) -> bool {
        assert_eq!(self.current_parent, usize::MAX);

        if self.root_size == root_size {
            return false;
        }
        self.root_size = root_size;

        return true;
    }

    pub fn mouse_move(&mut self, mx: f32, my: f32) -> bool {
        assert_eq!(self.current_parent, usize::MAX);

        if mx == self.mouse_pos[0] && my == self.mouse_pos[1] {
            return false;
        }
        self.mouse_pos = [mx, my];

        let hit = self.hit_test_filtered(mx, my, |hit| self.widgets[hit].props.pointer_events);

        if let Some(hit) = hit {
            self.hovered = hit.0;
        }
        else {
            self.hovered = 0;
        }

        return true;
    }

    pub fn mouse_down(&mut self, is_down: bool, button: MouseButton) -> bool {
        assert_eq!(self.current_parent, usize::MAX);

        if is_down == self.mouse_down[button as usize] {
            return false;
        }
        self.mouse_down[button as usize] = is_down;

        // @todo: check whether this event should be dispatched to any elements.
        //  - the capturing element.
        //  - the hovered element.
        //  - bubbling: any of their ancestors.
        let mut update = true;

        if is_down == false {
            if let Some((capture_button, _)) = self.mouse_capture {
                if capture_button == button {
                    self.mouse_capture = None;
                }
            }
        }

        if button == MouseButton::Left {
            let prev_active = self.active;

            if is_down {
                self.active = self.hovered;
            }
            else {
                self.active = 0;
            }

            update |= self.active != prev_active;
        }

        return update;
    }

    pub fn capture_mouse(&mut self, events: &WidgetEvents) -> bool {
        let button =
            if      events.mouse_went_down(MouseButton::Left)   { MouseButton::Left }
            else if events.mouse_went_down(MouseButton::Middle) { MouseButton::Middle }
            else if events.mouse_went_down(MouseButton::Right)  { MouseButton::Right }
            else { return false };

        if self.mouse_capture.is_none() {
            self.mouse_capture_pos = events.local_mouse_pos();
            self.mouse_capture = Some((button, events.widget));
            return true;
        }

        false
    }

    #[inline(always)]
    pub fn mouse_capture_pos(&self) -> [f32; 2] {
        self.mouse_capture_pos
    }

    pub fn has_mouse_capture(&self, events: &WidgetEvents) -> bool {
        matches!(self.prev_mouse_capture, Some((_, widget)) if widget == events.widget)
    }


    #[inline]
    pub fn edit_props_no_render(&mut self, events: &WidgetEvents) -> &mut Props {
        &mut self.widgets[events.widget as usize].props
    }

    pub fn set_scroll_pos(&mut self, info: &ScrollbarInfo, pos: [f32; 2]) {
        let widget = &mut self.widgets[info.parent as usize];

        let old_scroll_pos = widget.scroll_pos;
        let new_scroll_pos = [
            pos[0].clamp(0.0, (widget.content_max[0] - (widget.size[0] - info.scrollbar_sizes[1])).max(0.0)).floor(),
            pos[1].clamp(0.0, (widget.content_max[1] - (widget.size[1] - info.scrollbar_sizes[0])).max(0.0)).floor(),
        ];
        widget.scroll_pos = new_scroll_pos;

        if new_scroll_pos != old_scroll_pos {
            self.needs_update = true;
        }
    }

    pub fn mark_for_render(&mut self, events: &WidgetEvents) {
        _ = events;
        self.needs_render = true;
    }

    #[inline(always)]
    pub fn needs_render(&self) -> bool {
        self.needs_render
    }
}


struct ChildRenderer {
    merge_text: bool,
    first: OptWidgetId,
    last:  OptWidgetId,
    counter: u32,
    text_layout: Option<(TextLayout, OptWidgetId, OptWidgetId)>,
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
        if let Some((layout, first_render_child, last_render_child)) = self.text_layout.take() {
            let key = KeyData::TextLayout(self.counter);
            self.counter += 1;

            let data = TextLayoutData { layout, first_render_child, last_render_child };

            let widget = gui.alloc_widget(key, Props::new(), WidgetData::TextLayout(data));
            self.append(widget, gui);
        }
    }

    fn visit(&mut self, child: NonZeroU32, gui: &mut Gui) -> OptWidgetId {
        let widget = &mut gui.widgets[child.get() as usize];
        let next = widget.next_sibling;

        match &mut widget.data {
            WidgetData::Box(_) => {
                self.flush(gui);
                self.append(child, gui);
            }

            WidgetData::Text(text) => {
                // kinda wanna flush here,
                // but can't borrow gui as mutable.
                // oh well, just don't break it, ok?
                if self.text_layout.is_none() {
                    self.text_layout = Some((
                        TextLayout::new(&gui.fonts),
                        None.into(), None.into()
                    ));
                }
                else { debug_assert!(self.merge_text) }

                let (layout, first_ren, last_ren) = self.text_layout.as_mut().unwrap();

                // add text.
                text.layout_begin = layout.text().len() as u32;
                layout.append(
                    &text.text,
                    widget.props.font_face,
                    widget.props.font_size,
                    widget.props.text_color,
                    child.get());
                text.layout_end = layout.text().len() as u32;

                // update render child list.
                widget.prev_render_sibling = None;
                widget.next_render_sibling = None;
                if let Some(last) = last_ren {
                    widget.prev_render_sibling = Some(*last);
                    gui.widgets[last.get() as usize].next_render_sibling = Some(child);
                }

                if first_ren.is_none() {
                    *first_ren = Some(child);
                }
                *last_ren = Some(child);


                if !self.merge_text {
                    self.flush(gui);
                }
            }

            WidgetData::TextLayout(_) | WidgetData::Free(_) => unreachable!()
        }

        next
    }
}

