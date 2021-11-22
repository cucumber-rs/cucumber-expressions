#![no_main]
use cucumber_expressions::parse::alternation;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(str) = std::str::from_utf8(data) {
        let _ = alternation(str);
    }
});
