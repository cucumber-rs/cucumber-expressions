#![no_main]

use cucumber_expressions::Expression;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &str| {
    let _ = Expression::regex(data);
});
