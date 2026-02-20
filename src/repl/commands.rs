pub enum ReplCommand<'a> {
    Quit,
    Help,
    Type(&'a str),
    Info(&'a str),
    Sig(&'a str),
    Doc(&'a str),
    Source(&'a str),
    Sexp(&'a str),
    Ast(&'a str),
    Clif(&'a str),
    Disasm(&'a str),
    Time(&'a str),
    Mem(&'a str),
    List(&'a str),
    Imports(&'a str),
    Expand(&'a str),
    Mod(&'a str),
    Reload(&'a str),
    Exe(&'a str),
}

pub fn parse_repl_command(input: &str) -> Option<ReplCommand<'_>> {
    let trimmed = input.trim();
    if !trimmed.starts_with('/') {
        return None;
    }
    let rest = &trimmed[1..];
    let (cmd, arg) = match rest.find(char::is_whitespace) {
        Some(i) => (&rest[..i], rest[i..].trim()),
        None => (rest, ""),
    };
    match cmd {
        "quit" | "q" => Some(ReplCommand::Quit),
        "help" | "h" => Some(ReplCommand::Help),
        "type" | "t" => Some(ReplCommand::Type(arg)),
        "info" | "i" => Some(ReplCommand::Info(arg)),
        "sig" | "s" => Some(ReplCommand::Sig(arg)),
        "doc" | "d" => Some(ReplCommand::Doc(arg)),
        "source" => Some(ReplCommand::Source(arg)),
        "sexp" => Some(ReplCommand::Sexp(arg)),
        "ast" => Some(ReplCommand::Ast(arg)),
        "clif" => Some(ReplCommand::Clif(arg)),
        "disasm" => Some(ReplCommand::Disasm(arg)),
        "time" => Some(ReplCommand::Time(arg)),
        "mem" | "m" => Some(ReplCommand::Mem(arg)),
        "list" | "l" => Some(ReplCommand::List(arg)),
        "imports" => Some(ReplCommand::Imports(arg)),
        "expand" | "e" => Some(ReplCommand::Expand(arg)),
        "mod" => Some(ReplCommand::Mod(arg)),
        "reload" | "r" => Some(ReplCommand::Reload(arg)),
        "exe" => Some(ReplCommand::Exe(arg)),
        _ => {
            eprintln!("Unknown command /{}, try /help", cmd);
            // Return Help so the REPL loop `continue`s
            Some(ReplCommand::Help)
        }
    }
}
