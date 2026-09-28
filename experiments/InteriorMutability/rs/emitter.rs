// An event emitter: handlers are `Box<dyn Fn(&Event)>`, registered on the emitter, and three of
// them share one `Rc<RefCell<Stats>>`. Events: click, key 65, click, key 66, click. Prints
// (3, 131, 5): clicks, the sum of key codes, and all events.
use std::cell::RefCell;
use std::rc::Rc;

enum Event {
    Click,
    Key(i32),
}

#[derive(Default)]
struct Stats {
    clicks: i32,
    keys: i32,
    all: i32,
}

#[derive(Default)]
struct Emitter {
    handlers: Vec<Box<dyn Fn(&Event)>>,
}

impl Emitter {
    fn on(&mut self, h: impl Fn(&Event) + 'static) {
        self.handlers.push(Box::new(h));
    }
    fn emit(&self, e: &Event) {
        for h in &self.handlers {
            h(e);
        }
    }
}

fn main() {
    let stats = Rc::new(RefCell::new(Stats::default()));
    let mut em = Emitter::default();
    let s = stats.clone();
    em.on(move |e| if let Event::Click = e { s.borrow_mut().clicks += 1 });
    let s = stats.clone();
    em.on(move |e| if let Event::Key(k) = e { s.borrow_mut().keys += k });
    let s = stats.clone();
    em.on(move |_| s.borrow_mut().all += 1);
    for e in [Event::Click, Event::Key(65), Event::Click, Event::Key(66), Event::Click] {
        em.emit(&e);
    }
    let st = stats.borrow();
    println!("({}, {}, {})", st.clicks, st.keys, st.all);
}
