use std::collections::HashMap;
use std::convert::TryInto;
use sv_parser_parser::{pp_parser, Span, SpanInfo};
use sv_parser_syntaxtree::{Locate, NodeEvent, RefNode};

pub fn preprocessor(s: &str) -> String {
    let mut ret = String::new();
    let pp_text = pp_parser(Span::new_extra(s, SpanInfo::default()));

    let mut skip = false;
    let mut skip_nodes = vec![];
    let mut defines = HashMap::new();

    if let Ok((_, pp_text)) = pp_text {
        for n in pp_text.into_iter().event() {
            match n {
                NodeEvent::Enter(RefNode::ResetallCompilerDirective(_)) if !skip => {
                    defines.clear();
                }
                NodeEvent::Enter(RefNode::UndefineCompilerDirective(x)) if !skip => {
                    let (_, _, ref name) = x.nodes;
                    let id = identifier((&name.nodes.0).into());
                    let id = String::from(id.unwrap().str(s));
                    defines.remove(&id);
                }
                NodeEvent::Enter(RefNode::UndefineallCompilerDirective(_)) if !skip => {
                    defines.clear();
                }
                NodeEvent::Enter(RefNode::SourceDescriptionNotDirective(x)) if !skip => {
                    let locate: Locate = x.try_into().unwrap();
                    ret.push_str(locate.str(s));
                }
                NodeEvent::Enter(RefNode::IfdefDirective(x)) if !skip => {
                    let (_, _, ref ifid, ref ifbody, ref elsif, ref elsebody, _, _) = x.nodes;
                    let ifid = identifier(ifid.into());
                    let ifid = String::from(ifid.unwrap().str(s));
                    let mut hit = false;
                    if defines.contains_key(&ifid) {
                        hit = true;
                    } else {
                        skip_nodes.push(ifbody.into());
                    }

                    for x in elsif {
                        let (_, _, ref elsifid, ref elsifbody) = x;
                        let elsifid = identifier(elsifid.into());
                        let elsifid = String::from(elsifid.unwrap().str(s));
                        if hit {
                            skip_nodes.push(elsifbody.into());
                        } else if defines.contains_key(&elsifid) {
                            hit = true;
                        } else {
                            skip_nodes.push(elsifbody.into());
                        }
                    }

                    if let Some(elsebody) = elsebody {
                        let (_, _, ref elsebody) = elsebody;
                        if hit {
                            skip_nodes.push(elsebody.into());
                        }
                    }
                }
                NodeEvent::Enter(RefNode::IfndefDirective(x)) if !skip => {
                    let (_, _, ref ifid, ref ifbody, ref elsif, ref elsebody, _, _) = x.nodes;
                    let ifid = identifier(ifid.into());
                    let mut hit = false;
                    if !defines.contains_key(&String::from(ifid.unwrap().str(s))) {
                        hit = true;
                    } else {
                        skip_nodes.push(ifbody.into());
                    }

                    for x in elsif {
                        let (_, _, ref elsifid, ref elsifbody) = x;
                        let elsifid = identifier(elsifid.into());
                        if hit {
                            skip_nodes.push(elsifbody.into());
                        } else if defines.contains_key(&String::from(elsifid.unwrap().str(s))) {
                            hit = true;
                        } else {
                            skip_nodes.push(elsifbody.into());
                        }
                    }

                    if let Some(elsebody) = elsebody {
                        let (_, _, ref elsebody) = elsebody;
                        if hit {
                            skip_nodes.push(elsebody.into());
                        }
                    }
                }
                NodeEvent::Enter(RefNode::TextMacroDefinition(x)) if !skip => {
                    let (_, _, ref name, _) = x.nodes;
                    let id = identifier((&name.nodes.0).into());
                    let id = String::from(id.unwrap().str(s));
                    defines.insert(id, x.clone());
                }
                NodeEvent::Enter(x) => {
                    if skip_nodes.contains(&x) {
                        skip = true;
                    }
                }
                NodeEvent::Leave(x) => {
                    if skip_nodes.contains(&x) {
                        skip = false;
                    }
                }
            }
        }
    }
    //let ret = dbg!(ret);
    println!("{}", ret);

    ret
}

fn identifier(node: RefNode) -> Option<Locate> {
    for x in node {
        match x {
            RefNode::SimpleIdentifier(x) => {
                let x: Locate = x.nodes.0.try_into().unwrap();
                return Some(x);
            }
            RefNode::EscapedIdentifier(x) => {
                let x: Locate = x.nodes.0.try_into().unwrap();
                return Some(x);
            }
            _ => (),
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let s = r##"module and_op (a, b, c);
                  output a;
                  input b, c;

                  `define behavioral
                  `ifdef behavioral
                    wire a = b & c;
                  `else
                    and a1 (a,b,c);
                  `endif
                endmodule"##;
        preprocessor(s);
    }
}
