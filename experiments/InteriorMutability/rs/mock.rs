// The Rust Book's mock (ch15-05): `LimitTracker` sends messages through `&dyn Messenger`, whose
// `send` takes `&self`, so the mock records the messages in a `RefCell<Vec<_>>`. Messages are
// codes here: 75 (warning), 90 (urgent), 100 (over quota). Values 50, 80, 95 and 100 against a
// maximum of 100. Prints (3, 75, 100): three messages, the first and the last.
use std::cell::RefCell;

trait Messenger {
    fn send(&self, code: i32);
}

struct LimitTracker<'a, T: Messenger> {
    messenger: &'a T,
    max: i32,
}

impl<'a, T: Messenger> LimitTracker<'a, T> {
    fn set_value(&self, value: i32) {
        let pct = value * 100 / self.max;
        if pct >= 100 {
            self.messenger.send(100);
        } else if pct >= 90 {
            self.messenger.send(90);
        } else if pct >= 75 {
            self.messenger.send(75);
        }
    }
}

struct MockMessenger {
    sent: RefCell<Vec<i32>>,
}

impl Messenger for MockMessenger {
    fn send(&self, code: i32) {
        self.sent.borrow_mut().push(code);
    }
}

fn main() {
    let mock = MockMessenger { sent: RefCell::new(vec![]) };
    let t = LimitTracker { messenger: &mock, max: 100 };
    for v in [50, 80, 95, 100] {
        t.set_value(v);
    }
    let s = mock.sent.borrow();
    println!("({}, {}, {})", s.len(), s[0], s[s.len() - 1]);
}
