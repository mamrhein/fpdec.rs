// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use criterion::{criterion_group, criterion_main, Criterion};
use fpdec::Decimal;
use order::{Order, OrderBuilder, OrderCalculator, ORDER_DETAILS};

pub fn criterion_benchmark(c: &mut Criterion) {
    let order = Order::<Decimal>::build_order(&ORDER_DETAILS);
    c.bench_function("fpd_calc_order", |b| b.iter(|| order.calc_order()));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
