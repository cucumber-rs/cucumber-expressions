#![no_main]

use cucumber_expressions::parse;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &str| {
    let _ = parse::expression(data);
});
