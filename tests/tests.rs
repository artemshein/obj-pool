use obj_pool::optional; // must be available

#[test]
fn test_compile() {
    let _ = optional::some(10);
}