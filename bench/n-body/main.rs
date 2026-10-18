// N-body (the Benchmarks Game's): the Jovian planets and the sun, advanced `n` steps of 0.01
// days by the symplectic integrator. Prints the energy before and after, times 10⁹ and
// truncated, so that every side prints the same digits.

const PI: f64 = 3.141592653589793;
const SOLAR_MASS: f64 = 4.0 * PI * PI;
const DAYS: f64 = 365.24;

#[derive(Clone, Copy)]
struct Body {
    pos: [f64; 3],
    vel: [f64; 3],
    mass: f64,
}

fn body(pos: [f64; 3], vel: [f64; 3], mass: f64) -> Body {
    Body { pos, vel: [vel[0] * DAYS, vel[1] * DAYS, vel[2] * DAYS], mass: mass * SOLAR_MASS }
}

fn bodies() -> [Body; 5] {
    [
        body([0.0, 0.0, 0.0], [0.0, 0.0, 0.0], 1.0),
        body(
            [4.84143144246472090e+00, -1.16032004402742839e+00, -1.03622044471123109e-01],
            [1.66007664274403694e-03, 7.69901118419740425e-03, -6.90460016972063023e-05],
            9.54791938424326609e-04,
        ),
        body(
            [8.34336671824457987e+00, 4.12479856412430479e+00, -4.03523417114321381e-01],
            [-2.76742510726862411e-03, 4.99852801234917238e-03, 2.30417297573763929e-05],
            2.85885980666130812e-04,
        ),
        body(
            [1.28943695621391310e+01, -1.51111514016986312e+01, -2.23307578892655734e-01],
            [2.96460137564761618e-03, 2.37847173959480950e-03, -2.96589568540237556e-05],
            4.36624404335156298e-05,
        ),
        body(
            [1.53796971148509165e+01, -2.59193146099879641e+01, 1.79258772950371181e-01],
            [2.68067772490389322e-03, 1.62824170038242295e-03, -9.51592254519715870e-05],
            5.15138902046611451e-05,
        ),
    ]
}

fn offset_momentum(b: &mut [Body; 5]) {
    let mut p = [0.0f64; 3];
    for bi in b.iter() {
        for k in 0..3 {
            p[k] += bi.vel[k] * bi.mass;
        }
    }
    for k in 0..3 {
        b[0].vel[k] = -p[k] / SOLAR_MASS;
    }
}

fn energy(b: &[Body; 5]) -> f64 {
    let mut e = 0.0;
    for (i, bi) in b.iter().enumerate() {
        let v = bi.vel;
        e += 0.5 * bi.mass * (v[0] * v[0] + v[1] * v[1] + v[2] * v[2]);
        for bj in &b[i + 1..] {
            let dx = bi.pos[0] - bj.pos[0];
            let dy = bi.pos[1] - bj.pos[1];
            let dz = bi.pos[2] - bj.pos[2];
            e -= bi.mass * bj.mass / (dx * dx + dy * dy + dz * dz).sqrt();
        }
    }
    e
}

fn advance(b: &mut [Body; 5], dt: f64) {
    for i in 0..5 {
        let (left, right) = b.split_at_mut(i + 1);
        let bi = &mut left[i];
        for bj in right.iter_mut() {
            let dx = bi.pos[0] - bj.pos[0];
            let dy = bi.pos[1] - bj.pos[1];
            let dz = bi.pos[2] - bj.pos[2];
            let d2 = dx * dx + dy * dy + dz * dz;
            let mag = dt / (d2 * d2.sqrt());
            let (mi, mj) = (bi.mass, bj.mass);
            bi.vel[0] -= dx * mj * mag;
            bi.vel[1] -= dy * mj * mag;
            bi.vel[2] -= dz * mj * mag;
            bj.vel[0] += dx * mi * mag;
            bj.vel[1] += dy * mi * mag;
            bj.vel[2] += dz * mi * mag;
        }
    }
    for bi in b.iter_mut() {
        for k in 0..3 {
            bi.pos[k] += dt * bi.vel[k];
        }
    }
}

fn main() {
    let n: i32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(1000);
    let mut b = bodies();
    offset_momentum(&mut b);
    println!("{}", (energy(&b) * 1e9) as i64);
    for _ in 0..n {
        advance(&mut b, 0.01);
    }
    println!("{}", (energy(&b) * 1e9) as i64);
}
