// AWFY Bounce, as awfy/bounce.bc: 100 balls from AWFY's Random, 50 passes, count bounces (1331).
rs::counting!();
struct Ball { x: i32, y: i32, xv: i32, yv: i32 }
impl Ball {
    fn bounce(&mut self) -> bool {
        let mut hit = false;
        self.x += self.xv; self.y += self.yv;
        if self.x > 500 { self.x = 500; self.xv = -self.xv.abs(); hit = true }
        if self.x < 0 { self.x = 0; self.xv = self.xv.abs(); hit = true }
        if self.y > 500 { self.y = 500; self.yv = -self.yv.abs(); hit = true }
        if self.y < 0 { self.y = 0; self.yv = self.yv.abs(); hit = true }
        hit
    }
}
fn next(s: &mut i32) -> i32 { *s = (s.wrapping_mul(1309).wrapping_add(13849)) & 65535; *s }
fn main() {
    let s0 = rs::snap();
    let mut seed = 74755;
    let mut balls: Vec<Ball> = (0..100).map(|_| {
        let (a, b, c, d) = (next(&mut seed), next(&mut seed), next(&mut seed), next(&mut seed));
        Ball { x: a % 500, y: b % 500, xv: c % 300 - 150, yv: d % 300 - 150 }
    }).collect();
    let mut bounces = 0;
    for _ in 0..50 { for b in balls.iter_mut() { if b.bounce() { bounces += 1 } } }
    rs::report(s0);
    println!("{}", bounces);
}
