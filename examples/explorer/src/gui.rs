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

    pub fill: bool,
    pub fill_color: u32,

    pub pointer_events: bool,
}

impl Props {
    #[inline(always)]
    pub fn new() -> Props { Props::default() }

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
    key:       KeyData,
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
}

enum WidgetData {
    Box        (BoxData),
    TextLayout (TextLayoutData),
    Text       (TextData),
}

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
    layout: TextLayout<u32>,
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
    fn begin(&mut self, props: Props, data: WidgetData) {
        self.props = props;
        self.data  = data;
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
    widgets: Vec<Widget>,
    hash:    Vec<OptWidgetId>,

    current_parent:  usize,
    current_counter: u32,

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
        };

        Gui {
            widgets:   vec![root],
            hash:    vec![None; 16],

            current_parent:  usize::MAX,
            current_counter: 0,

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

            match &widget.data {
                WidgetData::Box(data) => {
                    let mut at = data.first_render_child;
                    while let Some(current) = at {
                        let current = current.get() as usize;
                        let result = rec(this, current, xx, yy);
                        if result.is_some() {
                            return result;
                        }

                        at = this.widgets[current].next_render_sibling;
                    }
                }

                WidgetData::TextLayout(data) => {
                    // @todo: map spans & return hit widget.
                    let _ = data;
                }

                WidgetData::Text(_) => unreachable!()
            }

            return Some(WidgetId(widget_index as u32));
        }

        rec(self, 0, x, y)
    }


    pub fn begin(&mut self) {
        assert_eq!(self.current_parent, usize::MAX);
        self.current_parent  = 0;
        self.current_counter = 0;
        self.widgets[0].begin(Props::default(), WidgetData::Box(BoxData::default()));
    }

    pub fn end(&mut self) {
        assert_eq!(self.current_parent, 0);
        self.render_children();
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
                self.widgets[widget.get() as usize].begin(props, data);
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
                    hash_next,

                    props,
                    data,

                    parent:       self.current_parent as u32,
                    prev_sibling: None,
                    next_sibling: None,
                    prev_render_sibling: None,
                    next_render_sibling: None,

                    pos:  [0.0; 2],
                    size: [0.0; 2],
                });

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
        let mut cr = ChildRenderer::new();
        let mut at = self.widgets[self.current_parent].box_data().first_child;
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
        fn rec(this: &mut Gui, widget_index: usize) {
            let widget = &mut this.widgets[widget_index];

            let size = match &mut widget.data {
                WidgetData::Box(data) => {
                    let mut width  = 0f32;
                    let mut height = 0f32;

                    let mut at = data.first_render_child;
                    while let Some(current) = at {
                        let current = current.get() as usize;
                        rec(this, current);

                        let child = &mut this.widgets[current];
                        child.pos = [0., height];

                        width   = width.max(child.size[0]);
                        height += child.size[1];

                        at = child.next_render_sibling;
                    }

                    [width, height]
                }

                WidgetData::TextLayout(data) => {
                    data.layout.size()
                }

                WidgetData::Text(_) => unreachable!()
            };

            this.widgets[widget_index].size = size;
        }

        rec(self, 0);
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

                WidgetData::Text(_) => unreachable!()
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


struct ChildRenderer {
    first: OptWidgetId,
    last:  OptWidgetId,
    counter: u32,
    text_layout: Option<TextLayout<u32>>,
}

impl ChildRenderer {
    fn new() -> ChildRenderer {
        ChildRenderer { first: None, last: None, counter: 0, text_layout: None }
    }

    fn current_text_layout(&mut self, fonts: &FontCtx) -> &mut TextLayout<u32> {
        if self.text_layout.is_none() {
            self.text_layout = Some(TextLayout::new(fonts));
        }
        self.text_layout.as_mut().unwrap()
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
                self.current_text_layout(&gui.fonts).append_ex(
                    &text.text,
                    widget.props.font_face,
                    widget.props.font_size,
                    widget.props.text_color);
            }

            WidgetData::TextLayout(_) => unreachable!()
        }

        next
    }
}

