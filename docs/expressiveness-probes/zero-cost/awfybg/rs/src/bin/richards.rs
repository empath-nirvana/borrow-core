// AWFY Richards, index form: task control blocks in a Vec<Tcb>, packets in a Vec<Packet>,
// links are Option<usize>; the task function is an enum dispatched by match (as AWFY's
// per-task closures, without dyn). Same run as awfy/richards.bc: idler count 10000,
// answer (queuePacketCount, holdCount) = (23246, 9297).
rs::counting!();

const IDLER: usize = 0;
const WORKER: usize = 1;
const HANDLER_A: usize = 2;
const HANDLER_B: usize = 3;
const DEVICE_A: usize = 4;
const DEVICE_B: usize = 5;
const DEVICE_PACKET_KIND: i32 = 0;
const WORK_PACKET_KIND: i32 = 1;

struct Packet { link: Option<usize>, identity: usize, kind: i32, datum: usize, data: [usize; 4] }

enum Data {
    Idle { control: i32, count: i32 },
    Worker { destination: usize, count: usize },
    Handler { work_in: Option<usize>, device_in: Option<usize> },
    Device { pending: Option<usize> },
}

struct Tcb {
    link: Option<usize>, identity: usize, priority: i32, input: Option<usize>,
    packet_pending: bool, task_waiting: bool, task_holding: bool, data: Data,
}

struct Sched {
    tasks: Vec<Tcb>, // indexed by identity
    by_id: [Option<usize>; 6],
    packets: Vec<Packet>,
    task_list: Option<usize>,
    current: Option<usize>,
    current_id: usize,
    queue_count: i32,
    hold_count: i32,
}

impl Sched {
    fn add_last(&mut self, k: usize, q: Option<usize>) -> Option<usize> {
        self.packets[k].link = None;
        match q {
            None => Some(k),
            Some(h) => {
                let mut n = h;
                while let Some(nx) = self.packets[n].link { n = nx; }
                self.packets[n].link = Some(k);
                Some(h)
            }
        }
    }
    fn packet(&mut self, link: Option<usize>, identity: usize, kind: i32) -> Option<usize> {
        self.packets.push(Packet { link, identity, kind, datum: 0, data: [0; 4] });
        Some(self.packets.len() - 1)
    }
    fn create(&mut self, id: usize, pri: i32, wkq: Option<usize>, pp: bool, tw: bool, data: Data) {
        let t = self.tasks.len();
        self.tasks.push(Tcb { link: self.task_list, identity: id, priority: pri, input: wkq,
            packet_pending: pp, task_waiting: tw, task_holding: false, data });
        self.task_list = Some(t);
        self.by_id[id] = Some(t);
    }
    fn hold_self(&mut self) -> Option<usize> {
        self.hold_count += 1;
        let c = self.current.unwrap();
        self.tasks[c].task_holding = true;
        self.tasks[c].link
    }
    fn wait(&mut self) -> Option<usize> {
        let c = self.current.unwrap();
        self.tasks[c].task_waiting = true;
        self.current
    }
    fn release(&mut self, id: usize) -> Option<usize> {
        let t = self.by_id[id]?;
        self.tasks[t].task_holding = false;
        if self.tasks[t].priority > self.tasks[self.current.unwrap()].priority { Some(t) } else { self.current }
    }
    fn add_input(&mut self, t: usize, k: usize) -> Option<usize> {
        let c = self.current;
        match self.tasks[t].input {
            None => {
                self.tasks[t].input = Some(k);
                self.tasks[t].packet_pending = true;
                if self.tasks[t].priority > self.tasks[c.unwrap()].priority { Some(t) } else { c }
            }
            q => { let q2 = self.add_last(k, q); self.tasks[t].input = q2; c }
        }
    }
    fn queue_packet(&mut self, k: usize) -> Option<usize> {
        let t = self.by_id[self.packets[k].identity]?;
        self.queue_count += 1;
        self.packets[k].link = None;
        self.packets[k].identity = self.current_id;
        self.add_input(t, k)
    }
    fn run_task(&mut self, t: usize) -> Option<usize> {
        let msg = if self.tasks[t].packet_pending && self.tasks[t].task_waiting && !self.tasks[t].task_holding {
            let m = self.tasks[t].input.unwrap();
            let nx = self.packets[m].link;
            let tk = &mut self.tasks[t];
            tk.input = nx;
            tk.packet_pending = nx.is_some();
            tk.task_waiting = false;
            tk.task_holding = false;
            Some(m)
        } else { None };
        match self.tasks[t].data {
            Data::Idle { control, count } => {
                let count = count - 1;
                if count == 0 { self.tasks[t].data = Data::Idle { control, count }; return self.hold_self(); }
                if control & 1 == 0 {
                    self.tasks[t].data = Data::Idle { control: control / 2, count };
                    self.release(DEVICE_A)
                } else {
                    self.tasks[t].data = Data::Idle { control: (control / 2) ^ 53256, count };
                    self.release(DEVICE_B)
                }
            }
            Data::Worker { destination, count } => match msg {
                None => self.wait(),
                Some(w) => {
                    let d = if destination == HANDLER_A { HANDLER_B } else { HANDLER_A };
                    let mut c = count;
                    self.packets[w].identity = d;
                    self.packets[w].datum = 0;
                    for i in 0..4 {
                        c += 1;
                        if c > 26 { c = 1; }
                        self.packets[w].data[i] = c;
                    }
                    self.tasks[t].data = Data::Worker { destination: d, count: c };
                    self.queue_packet(w)
                }
            },
            Data::Handler { mut work_in, mut device_in } => {
                if let Some(w) = msg {
                    if self.packets[w].kind == WORK_PACKET_KIND { work_in = self.add_last(w, work_in); }
                    else { device_in = self.add_last(w, device_in); }
                }
                let r = match work_in {
                    None => { self.tasks[t].data = Data::Handler { work_in, device_in }; return self.wait(); }
                    Some(wi) => {
                        let count = self.packets[wi].datum;
                        if count < 4 {
                            match device_in {
                                None => { self.tasks[t].data = Data::Handler { work_in, device_in }; return self.wait(); }
                                Some(di) => {
                                    device_in = self.packets[di].link;
                                    self.packets[di].datum = self.packets[wi].data[count];
                                    self.packets[wi].datum = count + 1;
                                    self.tasks[t].data = Data::Handler { work_in, device_in };
                                    self.queue_packet(di)
                                }
                            }
                        } else {
                            work_in = self.packets[wi].link;
                            self.tasks[t].data = Data::Handler { work_in, device_in };
                            self.queue_packet(wi)
                        }
                    }
                };
                r
            }
            Data::Device { pending } => match msg {
                None => match pending {
                    None => self.wait(),
                    Some(p) => { self.tasks[t].data = Data::Device { pending: None }; self.queue_packet(p) }
                },
                Some(w) => { self.tasks[t].data = Data::Device { pending: Some(w) }; self.hold_self() }
            },
        }
    }
    fn schedule(&mut self) {
        self.current = self.task_list;
        while let Some(c) = self.current {
            let tk = &self.tasks[c];
            if tk.task_holding || (!tk.packet_pending && tk.task_waiting) {
                self.current = tk.link;
            } else {
                self.current_id = tk.identity;
                self.current = self.run_task(c);
            }
        }
    }
}

fn main() {
    let s0 = rs::snap();
    let mut s = Sched { tasks: Vec::with_capacity(6), by_id: [None; 6], packets: Vec::with_capacity(10),
        task_list: None, current: None, current_id: 0, queue_count: 0, hold_count: 0 };
    s.create(IDLER, 0, None, false, false, Data::Idle { control: 1, count: 10000 });
    let w = s.packet(None, 0, WORK_PACKET_KIND);
    let w = s.packet(w, 0, WORK_PACKET_KIND);
    s.create(WORKER, 1000, w, true, true, Data::Worker { destination: HANDLER_A, count: 0 });
    let w = s.packet(None, DEVICE_A, DEVICE_PACKET_KIND);
    let w = s.packet(w, DEVICE_A, DEVICE_PACKET_KIND);
    let w = s.packet(w, DEVICE_A, DEVICE_PACKET_KIND);
    s.create(HANDLER_A, 2000, w, true, true, Data::Handler { work_in: None, device_in: None });
    let w = s.packet(None, DEVICE_B, DEVICE_PACKET_KIND);
    let w = s.packet(w, DEVICE_B, DEVICE_PACKET_KIND);
    let w = s.packet(w, DEVICE_B, DEVICE_PACKET_KIND);
    s.create(HANDLER_B, 3000, w, true, true, Data::Handler { work_in: None, device_in: None });
    s.create(DEVICE_A, 4000, None, false, true, Data::Device { pending: None });
    s.create(DEVICE_B, 5000, None, false, true, Data::Device { pending: None });
    s.schedule();
    rs::report(s0);
    println!("{} {}", s.queue_count, s.hold_count);
}
