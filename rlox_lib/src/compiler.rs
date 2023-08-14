use crate::scanner::Scanner;

pub fn compile(source: String) {
    let scanner = Scanner::new(source.clone());
    let tokens = scanner.scan_tokens();

    let chars = source.as_bytes();

    for token in tokens {
        let mut token_string = String::new();
        let token_chars = &chars[token.start..token.start + token.length];
        for c in token_chars {
            token_string.push(c.to_owned() as char);
        }

        dbg!(token_string);
        dbg!(token);
    }
}
