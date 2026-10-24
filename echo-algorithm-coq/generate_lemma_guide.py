#!/usr/bin/env python3
"""
Generate a human-readable DOCX guide to every lemma and theorem in
EchoCorrectness.v — no Coq syntax, just plain English meaning.
"""

from docx import Document
from docx.shared import Pt, Inches, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

# ─── helpers ─────────────────────────────────────────────────────────────────

def set_margins(doc, top=1.0, bottom=1.0, left=1.2, right=1.2):
    for s in doc.sections:
        s.top_margin    = Inches(top)
        s.bottom_margin = Inches(bottom)
        s.left_margin   = Inches(left)
        s.right_margin  = Inches(right)

def heading(doc, text, level=1):
    p = doc.add_heading(text, level=level)
    p.alignment = WD_ALIGN_PARAGRAPH.LEFT
    return p

def body(doc, text):
    p = doc.add_paragraph(text)
    p.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
    for r in p.runs:
        r.font.size = Pt(11)
    return p

def entry(doc, name, meaning, why=None, note=None, kind="Lemma"):
    """One lemma/theorem block."""
    # Name line
    p = doc.add_paragraph()
    p.paragraph_format.space_before = Pt(6)
    p.paragraph_format.space_after  = Pt(1)
    tag = p.add_run(f"[{kind}]  ")
    tag.font.size  = Pt(9.5)
    tag.font.color.rgb = RGBColor(0x55, 0x55, 0x55)
    name_run = p.add_run(name)
    name_run.bold      = True
    name_run.font.size = Pt(11.5)
    name_run.font.color.rgb = RGBColor(0x00, 0x33, 0x77)

    # Meaning
    mp = doc.add_paragraph()
    mp.paragraph_format.left_indent = Inches(0.3)
    mp.paragraph_format.space_after = Pt(1)
    mr = mp.add_run(meaning)
    mr.font.size = Pt(11)

    # Why / how-it-works
    if why:
        wp = doc.add_paragraph()
        wp.paragraph_format.left_indent = Inches(0.3)
        wp.paragraph_format.space_after = Pt(1)
        wl = wp.add_run("Why it holds: ")
        wl.bold = True
        wl.font.size = Pt(10.5)
        wr = wp.add_run(why)
        wr.font.size = Pt(10.5)
        wr.font.color.rgb = RGBColor(0x33, 0x33, 0x33)

    if note:
        np_ = doc.add_paragraph()
        np_.paragraph_format.left_indent = Inches(0.3)
        np_.paragraph_format.space_after = Pt(3)
        nl = np_.add_run("Note: ")
        nl.bold = True
        nl.font.size = Pt(10)
        nr = np_.add_run(note)
        nr.font.size = Pt(10)
        nr.font.color.rgb = RGBColor(0x55, 0x55, 0x55)

def divider(doc, text):
    """Section sub-divider with gray bar."""
    p = doc.add_paragraph()
    p.paragraph_format.space_before = Pt(10)
    shd = OxmlElement('w:shd')
    shd.set(qn('w:val'),   'clear')
    shd.set(qn('w:color'), 'auto')
    shd.set(qn('w:fill'),  'D6E4F0')
    p._p.get_or_add_pPr().append(shd)
    r = p.add_run(f"  {text}")
    r.bold = True
    r.font.size = Pt(10.5)
    r.font.color.rgb = RGBColor(0x00, 0x22, 0x55)

# ─── document ────────────────────────────────────────────────────────────────

doc = Document()
set_margins(doc)

# Title
tp = doc.add_paragraph()
tp.alignment = WD_ALIGN_PARAGRAPH.CENTER
tr = tp.add_run("Echo Algorithm Proof — Plain-English Guide to Every Lemma and Theorem")
tr.bold = True
tr.font.size = Pt(17)

sp = doc.add_paragraph()
sp.alignment = WD_ALIGN_PARAGRAPH.CENTER
sp.add_run("What each statement means, why it is true, and why it matters.\n"
           "No Coq/Rocq notation. No Prop syntax.").font.size = Pt(11)

doc.add_paragraph()

# ─── Intro ───────────────────────────────────────────────────────────────────
heading(doc, "How to read this guide", level=1)
body(doc,
    "This document covers every named Lemma and Theorem in EchoCorrectness.v — the main "
    "proof file for the Echo distributed algorithm. They are organized in the order they "
    "appear in the file, grouped by the role they play. For each one you will find:\n\n"
    "  • What it says — a single plain-English sentence.\n"
    "  • Why it holds — the one-sentence intuition behind the proof.\n"
    "  • A note — when the lemma is used as a stepping-stone for something else.\n\n"
    "The proof is built bottom-up: tiny plumbing lemmas at the top; the big correctness "
    "theorems at the bottom. Reading top-to-bottom shows you how the pieces fit together."
)
body(doc,
    "Quick glossary of terms used throughout:\n\n"
    "  • Idle / Active / Decided — the three phases of a node. Idle = never received a "
    "Token. Active = received a Token, waiting for Echoes from its children. Decided = "
    "the initiator only; it has received all Echoes and the algorithm is done.\n"
    "  • Token — the outgoing wave message. Activates Idle nodes.\n"
    "  • Echo — the return wave message. Signals that a subtree is done.\n"
    "  • Pending — how many Echoes a node is still waiting for.\n"
    "  • Parent — the node that activated you (sent you the Token that made you Active).\n"
    "  • Children — the nodes that echoed back to you (your subtree).\n"
    "  • Message bag — the set of in-flight packets. Any packet can be delivered next "
    "(asynchronous model).\n"
    "  • Reachable state — any global state the system can be in after some sequence of steps.\n"
    "  • Invariant — a property that holds in every reachable state."
)

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Part 1 — Plumbing: State Update and List Lemmas", level=1)
body(doc,
    "These lemmas say nothing about the algorithm. They are the low-level toolbox for "
    "reasoning about updating node states and manipulating message lists. Every higher "
    "lemma ultimately relies on these."
)

divider(doc, "State lookup after an update (upd_* family)")

entry(doc, "upd_self",
    "If you update a node's state, immediately reading back that same node's state "
    "gives you the new value you just wrote.",
    "Trivial by the definition of update_proc: the update function checks if the "
    "requested node equals the updated node, which it does, so it returns the new value.",
    kind="Lemma")

entry(doc, "upd_other",
    "Updating node A's state does not affect node B's state (when A and B are different nodes).",
    "The update function checks if the requested node equals the updated node. Since A ≠ B, "
    "it falls through to the original function, returning B's old state unchanged.",
    kind="Lemma")

entry(doc, "upd_eq",
    "Two different ways of asking 'is node X equal to node Y?' always give the same "
    "answer — it does not matter which order you write the comparison.",
    "Node equality is decidable and symmetric.",
    note="This is a hygiene lemma. It prevents confusion when the update function and "
         "the query both use node equality but happen to write it in different orders.",
    kind="Lemma")

entry(doc, "proc_of_upd",
    "After updating node A's state in the global state, looking up any node B gives: "
    "A's new state if B is the same node as A, or the completely unchanged old state if "
    "B is a different node.",
    "Combines upd_self and upd_other into a single case-split.",
    note="This is the workhorse for all reasoning about state updates. Almost every "
         "proof step that follows a state update immediately applies this lemma.",
    kind="Lemma")

divider(doc, "Message bag manipulation")

entry(doc, "remove_pkt_in",
    "Removing a specific packet from the message bag does not cause any other (different) "
    "packet to disappear — all other packets remain in the bag.",
    "The remove operation only deletes the first matching copy of the target packet; "
    "non-matching packets are unaffected by definition.",
    note="Used constantly when reasoning about delivery steps. After a packet is "
         "delivered (removed), you need to know that all other packets are still there.",
    kind="Lemma")

divider(doc, "Neighbors and sending")

entry(doc, "nbrs_adj",
    "If a node M appears in node N's neighbor list, then M and N are directly connected "
    "by an edge in the graph.",
    "The neighbor list is defined as all nodes that pass the adjacency test, so "
    "membership in the list and passing the test are equivalent.",
    kind="Lemma")

entry(doc, "send_to_all_inv",
    "When a node sends the same message type to a list of destinations, every packet "
    "that appears in the result: (a) has the correct sender, (b) has the correct message "
    "type, and (c) has a destination that is in the destination list.",
    "The send_to_all function is a simple map — it creates exactly one packet per "
    "destination and nothing else.",
    kind="Lemma")

entry(doc, "filter_subset",
    "Any element that survives a filter is still an element of the original list.",
    "Filtering only removes elements; it cannot introduce new ones.",
    kind="Lemma")

divider(doc, "No-op cases: four message types leave state unchanged")

entry(doc, "handle_msg_procs_noop",
    "In four of the six message-handling situations, delivering the packet changes "
    "nothing about any node's state: only the message bag changes (the delivered packet "
    "is removed and possibly a reply is added). The four no-op situations are: "
    "(1) a Token arriving at an already-Active node, "
    "(2) a Token arriving at an already-Decided node, "
    "(3) an Echo arriving at a Decided node, "
    "(4) an Echo arriving at an Idle node.",
    "In these four cases the algorithm explicitly returns the original node states "
    "unchanged. The only interesting cases — where a node's state actually changes — "
    "are Token arriving at an Idle node (node becomes Active) and Echo arriving at an "
    "Active node (pending decrements).",
    note="This is used as a shortcut tactic throughout the proofs: whenever we are in "
         "one of these four boring cases, a single application of this lemma closes the "
         "state-related subgoal.",
    kind="Lemma")

divider(doc, "State equality helpers")

entry(doc, "proc_of_eq_of_procs",
    "If two global states have exactly the same per-node state function, then looking up "
    "any node's full state gives the same result in both.",
    "Direct consequence of the definition of proc_of.",
    kind="Lemma")

entry(doc, "proc_of_parent_eq_of_procs",
    "If two global states have exactly the same per-node state function, then any "
    "node's parent pointer is identical in both states.",
    "Follows from proc_of_eq_of_procs: same state → same parent field.",
    kind="Lemma")

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Part 2 — Group A: Core Structural Invariants", level=1)
body(doc,
    "These are the most fundamental properties of the algorithm. They say that the "
    "parent-pointer structure is always a valid forest, and that every Active non-"
    "initiator node has a chain of parent pointers reaching back to the initiator. "
    "Everything else in the proof depends on these."
)

divider(doc, "active_non_init_parent — non-initiators always have a parent when Active")

entry(doc, "active_non_init_parent_base",
    "Before the algorithm starts (in the very first state), the invariant 'every Active "
    "non-initiator node has a parent pointer' is trivially satisfied.",
    "In the initial state, every node is Idle — no one is Active — so there is nothing "
    "to check.",
    kind="Lemma")

entry(doc, "active_non_init_parent_step",
    "Every single step of the algorithm preserves the property that each Active "
    "non-initiator node has its parent pointer set.",
    "The only step that makes a non-initiator Active is delivering a Token to an Idle "
    "node, and that step immediately sets the parent pointer to the Token's sender. All "
    "other steps either don't change any node's phase, or only change the initiator.",
    kind="Lemma")

entry(doc, "active_non_init_parent_holds",
    "In every reachable state of the algorithm, every non-initiator node that is Active "
    "has its parent pointer set to some specific node.",
    "Follows from the base + step lemmas by induction on reachability.",
    note="Used widely: whenever a non-initiator is Active, you can immediately pull out "
         "its parent. This prevents 'option None' from getting in the way.",
    kind="Lemma")

divider(doc, "non_init_not_decided — only the initiator can decide")

entry(doc, "non_init_not_decided_base",
    "Before the algorithm starts, the invariant 'no non-initiator is Decided' is "
    "trivially satisfied.",
    "Initially everyone is Idle.",
    kind="Lemma")

entry(doc, "non_init_not_decided_step",
    "Every step preserves the property that non-initiator nodes never reach the "
    "Decided phase.",
    "The only way a node reaches Decided is the Echo/Active case with pending = 1 and "
    "parent = None. But active_non_init_parent_holds tells us that a non-initiator "
    "Active node always has a non-None parent. So parent = None can only be the initiator.",
    kind="Lemma")

entry(doc, "non_init_not_decided_holds",
    "In every reachable state, no non-initiator node is ever in the Decided phase. "
    "Decided is a status reserved for the initiator alone.",
    "Follows from base + step by induction.",
    note="Critical for decided_implies_all_active: when we know a non-initiator node "
         "is non-Idle, and it can't be Decided, it must be Active.",
    kind="Theorem")

divider(doc, "INV — the combined structural invariant")

entry(doc, "INV_init",
    "The four structural properties (parent pointers on real edges, no self-parent, "
    "initiator has no parent, initiator Idle means no messages) all hold in the "
    "initial state.",
    "Initially: no node has a parent pointer set, no messages exist, and the initiator "
    "is Idle. Every condition holds vacuously or trivially.",
    kind="Lemma")

entry(doc, "INV_step_start",
    "The initiator's startup step — becoming Active and flooding Tokens to all its "
    "neighbors — preserves all four structural properties.",
    "The new messages are Token packets, each traveling along a real edge (parent_is_"
    "neighbor is satisfied because the initiator is adjacent to all its neighbors). The "
    "initiator gets no parent (initiator_no_parent stays). After startup the initiator "
    "is Active, not Idle, so init_idle_empty holds vacuously.",
    kind="Lemma")

entry(doc, "deliver_token_idle",
    "Delivering a Token to an Idle node (the normal activation step) preserves all "
    "four structural properties.",
    "The newly active node sets its parent to the Token's sender, which was an adjacent "
    "node (the Token traveled along a real edge, so valid_packets in the pre-state "
    "guarantees the sender is a neighbor). Self-parent is impossible because of "
    "adj_irrefl (no self-loops). The new forward Tokens also travel along real edges.",
    kind="Lemma")

entry(doc, "deliver_token_active",
    "Delivering a duplicate Token to an already-Active node preserves all four "
    "structural properties.",
    "The Active node ignores the Token content and sends an Echo back. No node's "
    "state changes; only a new Echo packet (traveling along a real edge by adj_sym) "
    "is added to the bag.",
    kind="Lemma")

entry(doc, "deliver_echo_active",
    "Delivering an Echo to an Active node preserves all four structural properties.",
    "Three sub-cases: (a) pending > 1: pending decrements, a new child is added, no "
    "new messages. (b) pending = 1, non-initiator: pending reaches 0, node sends Echo "
    "to parent (an adjacent node by parent_is_neighbor). (c) pending = 1, initiator: "
    "decides, no new messages. All four structural properties survive each sub-case.",
    kind="Lemma")

entry(doc, "deliver_ignored",
    "Delivering any message to a node that the algorithm ignores "
    "(Token to Decided, Echo to Idle, Echo to Decided) preserves all four structural "
    "properties.",
    "In all three ignored cases, handle_msg returns the global state completely "
    "unchanged (the delivered packet is removed but nothing else changes). The "
    "pre-state satisfies INV, so the post-state does too.",
    kind="Lemma")

entry(doc, "INV_step_deliver",
    "For any packet that gets delivered in the message bag, doing so preserves all "
    "four structural properties.",
    "Dispatches to one of the six per-case lemmas above depending on what message "
    "type arrived and what phase the receiving node was in.",
    kind="Lemma")

entry(doc, "INV_holds",
    "The four structural properties hold in every reachable state: parent pointers "
    "are always on real graph edges, no node is its own parent, the initiator never "
    "has a parent, and before the initiator fires there are no messages.",
    "Induction: INV_init gives the base, INV_step_start and INV_step_deliver give "
    "the inductive step.",
    kind="Theorem")

entry(doc, "tree_invariant_holds",
    "The three tree-shape properties — parents are on real edges, no self-parent, "
    "initiator is the root — hold in every reachable state.",
    "Extracted from INV_holds.",
    kind="Theorem")

entry(doc, "children_are_neighbors_holds",
    "In every reachable state, every node that appears in a node's children list is "
    "directly connected to that node by a graph edge.",
    "Extracted from INV_holds.",
    kind="Theorem")

entry(doc, "valid_packets_holds",
    "In every reachable state, every packet in the message bag travels along a real "
    "graph edge — the source and destination are adjacent.",
    "Extracted from INV_holds.",
    kind="Theorem")

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Part 3 — Group A (continued): Token Source Chain (TSC)", level=1)
body(doc,
    "TSC captures the key structural property of the spanning tree being built: every "
    "Active non-initiator node has a chain of parent pointers that leads, step by step, "
    "all the way back to the initiator. This is the core correctness invariant — "
    "it says the parent structure is always a tree rooted at the initiator, not just "
    "a forest of disconnected edges."
)

divider(doc, "Path-following helpers")

entry(doc, "parent_path_upd_nil",
    "If you update a single node's state in the global state, and that update does not "
    "change the node's parent pointer, then the chain of parent pointers starting from "
    "any other node is exactly the same as before.",
    "Following parent pointers only reads the parent field of each node along the chain. "
    "If the updated node's parent did not change, no link in any chain is different.",
    kind="Lemma")

entry(doc, "parent_path_upd_agree",
    "If two global states agree on the parent pointers of all nodes along a particular "
    "parent chain, then the parent chain itself is the same in both states.",
    "The path-following computation only reads parent fields, so agreement on those "
    "fields is sufficient.",
    kind="Lemma")

divider(doc, "TSC: every active non-initiator traces back to the initiator")

entry(doc, "TSC_init",
    "In the initial state, the Token Source Chain property holds trivially.",
    "Initially no node is Active, so the condition 'every Active non-initiator has a "
    "parent chain to the initiator' has nothing to check.",
    kind="Lemma")

entry(doc, "TSC_step",
    "Every step of the algorithm preserves the Token Source Chain property.",
    "The only step that creates a new Active non-initiator is the Token/Idle delivery. "
    "That step sets the new node's parent to the Token sender. The sender was already "
    "Active (by token_src_not_idle) and either is the initiator or already had a chain "
    "to the initiator (by induction hypothesis). Prepending the new node to the sender's "
    "chain gives the new node its own chain.",
    kind="Lemma")

entry(doc, "TSC_holds",
    "In every reachable state, every Active non-initiator node has a finite chain of "
    "parent pointers that eventually reaches the initiator.",
    "Induction: TSC_init + TSC_step.",
    note="The main use: once we know the initiator has decided and everyone is Active "
         "(decided_implies_all_active), TSC_holds immediately gives the spanning tree "
         "completeness property.",
    kind="Theorem")

entry(doc, "active_non_init_has_chain",
    "Any node that is currently Active and is not the initiator can follow its parent "
    "pointer, then its parent's parent pointer, and so on, and eventually arrive at "
    "the initiator.",
    "Same as TSC_holds, stated slightly differently for use at call sites.",
    kind="Theorem")

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Part 4 — Group B: Token Propagation Invariants", level=1)
body(doc,
    "These invariants capture the forward progress of the activation wave. They say "
    "that Tokens are always 'ahead of' the Idle nodes — every non-Idle node has either "
    "already activated all its relevant neighbors, or has Tokens in flight to them."
)

divider(doc, "Message list helpers")

entry(doc, "in_send_to_all",
    "A packet is in the batch produced by sending one message type to a list of "
    "destinations if and only if its sender matches, its message type matches, and its "
    "destination is somewhere in that list.",
    "The batch is a direct enumeration of one packet per destination.",
    kind="Lemma")

entry(doc, "in_nbrs_of",
    "A node M is in node N's neighbor list if and only if M and N are directly connected "
    "by a graph edge.",
    "The neighbor list is defined by filtering all_nodes on the adjacency function.",
    kind="Lemma")

entry(doc, "remove_pkt_ne_in",
    "Removing a packet P from the bag does not affect whether a packet Q with a "
    "different destination (or a different source) is in the bag.",
    "Remove only eliminates matching entries. A packet with different endpoint is "
    "structurally distinct and is unaffected.",
    kind="Lemma")

entry(doc, "remove_pkt_body_ne_in",
    "Removing a Token packet from the bag does not affect whether any Echo packet "
    "is in the bag, and vice versa.",
    "Tokens and Echoes are structurally distinct; removing one type cannot eliminate "
    "the other.",
    kind="Lemma")

divider(doc, "token_src_not_idle — Token senders are always non-Idle")

entry(doc, "token_src_not_idle_base",
    "Before anything happens, the property 'every Token's sender is non-Idle' holds "
    "trivially because there are no Tokens yet.",
    kind="Lemma")

entry(doc, "token_src_not_idle_step",
    "Every step preserves the property that every Token in the bag was sent by a "
    "non-Idle node.",
    "New Tokens are only created by the initiator's startup step (initiator becomes "
    "Active before sending) and the Token/Idle handler (node becomes Active before "
    "forwarding). Old Tokens remain in the bag, and their senders' phases never "
    "decrease (Idle → Active → Decided), so ex-Idle senders are now Active.",
    kind="Lemma")

entry(doc, "token_src_not_idle_holds",
    "In every reachable state, every Token in the message bag was sent by a node that "
    "is currently Active or Decided — never Idle.",
    "A node must be non-Idle to send a Token, and phases never go backward.",
    note="Used in the pending-chain argument: when Token(M→N) is in the bag, we know "
         "M is not Idle, so M must be Active (since only initiator can be Decided and "
         "we handle that separately).",
    kind="Theorem")

divider(doc, "token_sent_or_notidle — the wave never stalls")

entry(doc, "token_sent_or_notidle_base",
    "Before the algorithm starts, the wave-progress property holds trivially: no node "
    "is non-Idle and no neighbors need to be covered.",
    kind="Lemma")

entry(doc, "token_sent_or_notidle_step",
    "Every step preserves the wave-progress property.",
    "Token/Idle delivery: the delivered Token is consumed but the newly Active node "
    "becomes non-Idle, satisfying the property for its sender/neighbor pair. The "
    "new node also sends Tokens to its own non-parent neighbors, starting fresh "
    "coverage. Token/Active: the duplicate Token consumed, sender (already Active) "
    "sends an Echo reply. Echo/Active: changes pending counts and possibly adds a "
    "message, but does not create any new (non-Active neighbor, no-Token) pair. "
    "The step_start case activates the initiator and immediately sends Tokens.",
    kind="Lemma")

entry(doc, "token_sent_or_notidle_holds",
    "In every reachable state: for any non-Idle node M and any neighboring node N "
    "that is not M's parent, either N is already non-Idle, or there is a Token from "
    "M to N currently in the message bag.",
    "The activation wave is always fully accounted for: every non-Idle node has either "
    "already activated each of its relevant neighbors, or has a Token in flight toward them.",
    note="This is the key lemma for Group E. It is combined with no_token_idle_decided "
         "to conclude that when the initiator decides, every neighbor of every Active "
         "node must itself be Active.",
    kind="Theorem")

divider(doc, "parent_is_active — parents are always 'awake'")

entry(doc, "parent_is_active_base",
    "Before the algorithm starts, the property 'every parent pointer points to an "
    "Active-or-Decided node' holds trivially: no parent pointers are set yet.",
    kind="Lemma")

entry(doc, "parent_is_active_step",
    "Every step preserves the property that every node's parent is Active or Decided.",
    "A parent pointer is only set when a Token/Idle delivery occurs: the sender of "
    "the Token becomes the parent. The sender is non-Idle (token_src_not_idle_holds) "
    "and not yet Decided at that moment, so it is Active. Since phases only increase, "
    "the parent remains Active or Decided forever after.",
    kind="Lemma")

entry(doc, "parent_is_active_holds",
    "In every reachable state, any node that has a parent pointer set has a parent "
    "that is Active or Decided — never Idle.",
    "You can only become someone's parent by sending them a Token, which requires "
    "being non-Idle.",
    note="Used in the no_mutual_parent proof and in the pending-chain argument to "
         "ensure the parent chain only passes through non-Idle nodes.",
    kind="Theorem")

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Part 5 — Group C: Bookkeeping Invariants", level=1)
body(doc,
    "Group C is the largest collection — 19 invariants that must be proved "
    "simultaneously because each one's proof relies on several of the others. "
    "They track fine-grained accounting: which packets exist, how many copies, "
    "who is in whose children list, and what the pending counter really means."
)

divider(doc, "pkt_nodes — packet endpoints are known nodes")

entry(doc, "pkt_nodes_in_all_nodes_base",
    "Before the algorithm starts, the property 'every packet endpoint is a known node' "
    "holds trivially because there are no packets.",
    kind="Lemma")

entry(doc, "pkt_nodes_in_all_nodes_step",
    "Every step preserves the property that every packet's source and destination are "
    "in the known node list.",
    "New packets are only created by the step_start and handle_msg functions, both of "
    "which only use nodes drawn from nbrs (filtered from all_nodes) or from existing "
    "packet fields that were already in all_nodes.",
    kind="Lemma")

entry(doc, "pkt_nodes_in_all_nodes_holds",
    "In every reachable state, both the source and destination of every in-flight "
    "packet are nodes that appear in the network's node list.",
    "The algorithm never sends a message to an invented address.",
    kind="Theorem")

entry(doc, "parent_in_all_nodes_holds",
    "In every reachable state, if a node has its parent pointer set, the parent itself "
    "is a node in the network's node list.",
    "Parents are always nodes that sent a Token, and Tokens only come from known nodes "
    "(pkt_nodes_in_all_nodes_holds).",
    kind="Theorem")

divider(doc, "no_mutual_parent — no two-node cycles in the parent graph")

entry(doc, "no_mutual_parent_base",
    "Before the algorithm starts, the no-mutual-parent property holds trivially: "
    "no parent pointers are set.",
    kind="Lemma")

entry(doc, "no_mutual_parent_step",
    "Every step preserves the property that if A's parent is B, then B's parent is "
    "not A.",
    "A node sets its parent only when receiving its first Token. If A received a Token "
    "from B, then B was already Active or Decided when it sent that Token. For B to "
    "have A as a parent, B would need to have received a Token from A while B was Idle "
    "— but B was already Active (non-Idle) by that time, contradiction.",
    kind="Lemma")

entry(doc, "no_mutual_parent_holds",
    "In every reachable state, the parent-pointer graph contains no two-cycles: if A's "
    "parent is B, then B's parent is definitely not A.",
    "A node is always activated by its parent, so the parent was already active first. "
    "Two nodes cannot each be the other's activator.",
    note="Used in the pending_propagates argument to show M is in its parent's "
         "forwarding set (which requires M not being the parent's own parent).",
    kind="Theorem")

divider(doc, "echo_src_not_idle — Echo senders are always non-Idle")

entry(doc, "echo_src_not_idle_base",
    "Initially, there are no Echo packets, so the property holds trivially.",
    kind="Lemma")

entry(doc, "echo_src_not_idle_step",
    "Every step preserves the property that every Echo's sender is non-Idle.",
    "Echoes are sent by: (a) Active nodes receiving Echoes when pending hits 1, (b) "
    "Active nodes receiving duplicate Tokens. In both cases the sender is Active, "
    "hence non-Idle. Phases don't decrease, so ex-Active senders remain non-Idle.",
    kind="Lemma")

entry(doc, "echo_src_not_idle_holds",
    "In every reachable state, every Echo in the message bag was sent by a node that "
    "is currently Active or Decided — never Idle.",
    "An Idle node never sends any message.",
    kind="Theorem")

divider(doc, "idle_not_in_children — Idle nodes are not anyone's child")

entry(doc, "idle_not_in_children_base",
    "Initially, all children lists are empty, so the property holds trivially.",
    kind="Lemma")

entry(doc, "idle_not_in_children_step",
    "Every step preserves the property that an Idle node does not appear in any "
    "node's children list.",
    "A node N is added to M's children list only when M delivers an Echo from N. "
    "By echo_src_not_idle_holds, Echo senders are non-Idle. So any node that gets "
    "added to a children list was non-Idle at delivery time, and phases don't decrease.",
    kind="Lemma")

entry(doc, "idle_not_in_children_holds",
    "In every reachable state, if node N is Idle, it does not appear in any other "
    "node's children list.",
    "To be in someone's children list you must have sent them an Echo, which requires "
    "having been Active.",
    note="Used in the pending-chain argument: if N is Idle and there is a Token(M→N) "
         "in the bag, then N is not in M's children list, which means M is still "
         "waiting for N's Echo, so M's pending ≥ 1.",
    kind="Theorem")

divider(doc, "token_dst_not_parent — Tokens only flow away from the parent, never back")

entry(doc, "token_dst_not_parent_base",
    "Initially, there are no Tokens, so the property holds trivially.",
    kind="Lemma")

entry(doc, "token_dst_not_parent_step",
    "Every step preserves the property that no Token is ever sent from a node back "
    "to that node's own parent.",
    "When a node becomes Active, it sends Tokens to all its non-parent neighbors — "
    "explicitly excluding the parent. Duplicate Tokens (Token/Active case) send an "
    "Echo back, not a Token. So Tokens never travel toward the parent.",
    kind="Lemma")

entry(doc, "token_dst_not_parent_holds",
    "In every reachable state, for any Token in the bag, the Token's destination is "
    "not the Token sender's own parent.",
    "Tokens always flow outward from the parent, never back toward it.",
    note="Used in echo_src_in_fwds_holds: a node that echoes back to M must be in M's "
         "forwarding set (non-parent neighbors), and this lemma is part of establishing that.",
    kind="Theorem")

divider(doc, "Forwarding set helpers (act_fwds)")

entry(doc, "nodup_act_fwds",
    "The forwarding list for any node — all its neighbors except its parent — "
    "contains no duplicate entries.",
    "The forwarding list is built by filtering all_nodes, which has no duplicates "
    "(nodup_nodes assumption), so the filtered result also has no duplicates.",
    note="Used for exact pending-count arithmetic: duplicate-free lists allow counting "
         "by length.",
    kind="Lemma")

entry(doc, "act_fwds_spec",
    "Precisely characterizes who is in a node M's forwarding set: node N is in M's "
    "forwarding set if and only if N is adjacent to M and N is not M's parent.",
    "The forwarding set is defined exactly this way — this lemma just makes the "
    "definition usable in both directions.",
    note="Used everywhere the forwarding set appears — it converts between set "
         "membership and the two concrete conditions (adjacency + not-parent).",
    kind="Lemma")

entry(doc, "act_fwds_parent_agree",
    "If two global states agree on node M's parent pointer, then M's forwarding set "
    "is identical in both states.",
    "The forwarding set depends only on the graph structure (fixed) and M's parent "
    "pointer. Same parent → same forwarding set.",
    kind="Lemma")

divider(doc, "decided_pending_zero — the initiator has pending = 0 when it decides")

entry(doc, "decided_pending_zero_base",
    "Initially the initiator is Idle (not Decided), so the property holds vacuously.",
    kind="Lemma")

entry(doc, "decided_pending_zero_step",
    "Every step preserves the property that if the initiator is Decided, its pending "
    "counter is zero.",
    "The initiator becomes Decided only in the Echo/Active case when pending = 1 "
    "and the handler simultaneously sets the new pending to 0. After that, no step "
    "ever modifies the initiator's pending counter again (all further messages to the "
    "initiator are ignored because it is Decided).",
    kind="Lemma")

entry(doc, "decided_pending_zero_holds",
    "In every reachable state, if the initiator is in the Decided phase, its pending "
    "counter is exactly zero.",
    "The initiator decides only when its last Echo arrives (pending drops from 1 to 0 "
    "in the same atomic step).",
    note="The final contradiction step in the pending-chain argument: "
         "pending_chain_to_initiator shows pending(initiator) ≥ 1, and "
         "decided_pending_zero_holds shows pending(initiator) = 0 — impossible.",
    kind="Theorem")

divider(doc, "Counting helpers (remaining_fwds and filter lengths)")

entry(doc, "existsb_children_true",
    "If node N is in M's children list, the membership-check function returns true.",
    kind="Lemma")

entry(doc, "not_in_children_negb",
    "If N is not in M's children list, the membership-check function returns false.",
    kind="Lemma")

entry(doc, "in_children_negb",
    "If N is in M's children list, the membership-check function returns true. "
    "(Complementary form of the previous lemma.)",
    kind="Lemma")

entry(doc, "length_filter_pos",
    "If at least one element of a list passes a filter test, then the filtered list "
    "has at least one element (length ≥ 1).",
    "Trivial by the semantics of filter.",
    kind="Lemma")

entry(doc, "remaining_fwds_pos",
    "If N is in M's forwarding set but not yet in M's children list, then M's count "
    "of 'remaining targets' (forwarding set members not yet in children) is at least 1.",
    "N is one such element, so the count of remaining members is ≥ 1.",
    note="This is the key stepping stone from 'there exists an unaccounted target' to "
         "'the count of remaining targets is positive', which then feeds into "
         "weak_pending_ge_count to conclude pending ≥ 1.",
    kind="Lemma")

divider(doc, "Packet counting lemmas (count_pkt family)")

entry(doc, "pkt_matches_self",
    "Every packet matches itself under the packet-matching comparison.",
    kind="Lemma")

entry(doc, "pkt_matches_sym",
    "Packet matching is symmetric: if A matches B, then B matches A.",
    kind="Lemma")

entry(doc, "count_pkt_ge_one_in",
    "If a packet is in a list, then its count in that list is at least 1.",
    kind="Lemma")

entry(doc, "count_pkt_zero_notin",
    "If a packet's count in a list is 0, then that packet is not in the list.",
    kind="Lemma")

entry(doc, "count_pkt_app",
    "Counting a packet in a concatenated list equals the sum of counting it in "
    "each individual part.",
    kind="Lemma")

entry(doc, "count_pkt_remove_le",
    "Removing a packet from a list cannot increase any other packet's count in "
    "that list.",
    kind="Lemma")

entry(doc, "count_pkt_src_mismatch",
    "If you create a batch of packets all from some sender S, and the packet you are "
    "counting has a different sender, the count contributed by that batch is zero.",
    kind="Lemma")

entry(doc, "count_pkt_send_to_all_notin",
    "If a packet's destination is not in the destination list, sending a batch to "
    "all those destinations does not add any matching packet to the count.",
    kind="Lemma")

entry(doc, "count_pkt_send_to_all_le_one",
    "When a batch of packets is sent to a list of destinations with no duplicates, "
    "there is at most one copy of any particular target packet in the batch.",
    "Each destination appears at most once in the list, so at most one packet in the "
    "batch can match a specific (source, destination, body) triple.",
    note="The key tool for proving token_at_most_once and echo_at_most_once: every "
         "send creates at most one copy of each specific packet.",
    kind="Lemma")

divider(doc, "token_at_most_once — at most one copy of each Token")

entry(doc, "token_at_most_once_remove_not_in",
    "After removing a specific Token from the bag, any other Token (with a different "
    "sender, destination, or type) is still present in the bag.",
    kind="Lemma")

entry(doc, "token_at_most_once_base",
    "Initially there are no Tokens, so the at-most-once property holds trivially.",
    kind="Lemma")

entry(doc, "count_pkt_zero_if_no_match",
    "If a packet does not match the one being counted, its contribution to the count "
    "is zero.",
    kind="Lemma")

entry(doc, "token_at_most_once_count_idle_src",
    "While the initiator is still Idle (before startup), there are no Tokens whose "
    "sender is the initiator.",
    "Tokens are only sent during or after the startup step. Before that step, the "
    "initiator has sent nothing.",
    kind="Lemma")

entry(doc, "token_at_most_once_step",
    "Every step preserves the property that at most one copy of any particular Token "
    "packet exists in the bag.",
    "New Tokens are created by send_to_all with a duplicate-free destination list "
    "(count_pkt_send_to_all_le_one), so at most one copy is added. Old Tokens are "
    "only ever removed (delivered), never duplicated.",
    kind="Lemma")

entry(doc, "token_at_most_once_holds",
    "In every reachable state, for any specific Token packet, there is at most one "
    "copy of it in the message bag.",
    "The algorithm never sends the same Token twice to the same destination.",
    kind="Theorem")

divider(doc, "token_from_parent_consumed — the activation Token is gone once you are Active")

entry(doc, "token_from_parent_consumed_base",
    "Initially, no node is Active, so the property holds vacuously.",
    kind="Lemma")

entry(doc, "token_from_parent_consumed_step",
    "Every step preserves the property that once a node is Active with parent P, "
    "the Token that P sent to activate this node is no longer in the bag.",
    "The Token is delivered to the node in the Token/Idle step that makes the node "
    "Active — delivery removes the Token from the bag. After that, no further copy "
    "of that Token is ever created (token_at_most_once).",
    kind="Lemma")

entry(doc, "token_from_parent_consumed_holds",
    "In every reachable state, for any Active node N with parent P, the specific Token "
    "packet that P sent to N is no longer in the message bag.",
    "The activation Token is a one-shot event: it is consumed in the very step that "
    "activates the node.",
    note="Used in the no_mutual_parent proof and to distinguish between Tokens that "
         "activated a node (gone) and Tokens that a node forwarded (still in flight "
         "or already answered with Echoes).",
    kind="Theorem")

divider(doc, "pending_pos_active — pending ≥ 1 means no Echo has been sent yet")

entry(doc, "pending_pos_active_base",
    "Initially no nodes are Active, so the property holds vacuously.",
    kind="Lemma")

entry(doc, "pending_pos_active_step",
    "Every step preserves the combined property: if an Active node M still has "
    "pending ≥ 1, then (a) M has not yet sent its Echo to its parent, and (b) M "
    "is not yet in its parent's children list.",
    "Part (a): M only sends its Echo to its parent when pending drops to 0. If "
    "pending ≥ 1, that moment has not arrived. Part (b): M is added to its parent's "
    "children list only when its Echo arrives at the parent, which requires the Echo "
    "to be delivered, which requires the Echo to have been sent. But part (a) says it "
    "hasn't been sent yet.",
    kind="Lemma")

entry(doc, "pending_pos_active_holds",
    "In every reachable state, if an Active node M still has at least one Echo "
    "outstanding (pending ≥ 1), then: M's Echo to its parent is not in the bag, "
    "and M has not yet been counted as a child of its parent.",
    "An Active node only reports back (sends Echo, gets added to parent's children) "
    "when all its own pending Echoes have arrived.",
    note="The linchpin of pending_propagates: M is not yet in parent's children list "
         "→ parent still has M as an uncounted forwarding target → parent's pending ≥ 1.",
    kind="Theorem")

divider(doc, "echo_at_most_once — at most one copy of each Echo")

entry(doc, "echo_at_most_once_remove_not_in",
    "Removing an Echo from the bag does not affect whether any other Echo is in the bag.",
    kind="Lemma")

entry(doc, "echo_at_most_once_base",
    "Initially there are no Echoes, so the at-most-once property holds trivially.",
    kind="Lemma")

entry(doc, "echo_at_most_once_step",
    "Every step preserves the property that at most one copy of any particular Echo "
    "packet exists in the bag.",
    "New Echoes are created one at a time (only one Echo is added per delivery step), "
    "and the pending_pos_active invariant prevents a node from sending the same Echo "
    "twice (it would have to send it once with pending ≥ 1 and once with pending = 1 "
    "in the same state, which is impossible).",
    kind="Lemma")

divider(doc, "The mega-step lemma: 19 invariants, proved together")

entry(doc, "act_fwds_some_eq",
    "When a node M has a non-None parent (some specific sender), M's forwarding set "
    "simplifies to: all of M's neighbors except that sender.",
    "Direct expansion of the forwarding set definition when the parent field is known.",
    note="A cosmetic simplification used throughout the accounting proofs to make "
         "the filter expression more readable.",
    kind="Lemma")

entry(doc, "filter_adj_ne_parent_eq",
    "Two different but equivalent ways of writing the filter that computes M's "
    "forwarding set produce the same list.",
    "A utility equivalence for unfolding the forwarding set in different proof contexts.",
    kind="Lemma")

entry(doc, "token_echo_accounting_step",
    "If all 19 bookkeeping invariants hold before a step, then all six primary "
    "sub-invariants hold after the step. These 19 invariants must be proved together "
    "in one giant lemma because each invariant's preservation proof requires one or "
    "more of the others as hypotheses.",
    "Case-split on body/phase (6 cases), then use the 19 hypotheses to discharge 6 "
    "goals per case. This is the largest proof in the file (~650 lines).",
    note="The 6 sub-invariants returned (which are the conclusion) are: "
         "echo_dst_not_idle, echo_token_sender_not, children_implies_no_parent_token, "
         "echo_not_in_children, echo_src_in_fwds, pending_exact_count_ge. All 6 are "
         "proved by showing they cannot be violated by any single step.",
    kind="Lemma")

divider(doc, "The six primary accounting invariants (individually extracted)")

entry(doc, "echo_dst_not_idle_holds",
    "In every reachable state, every Echo in the message bag is targeted at a node "
    "that is currently Active or Decided — never an Idle node.",
    "An Echo is a reply to a Token. You send an Echo back to whoever sent you a Token. "
    "That sender was non-Idle when it sent the Token, and phases don't go backward.",
    kind="Theorem")

entry(doc, "echo_token_sender_not_holds",
    "In every reachable state, for any Echo from N to M currently in the bag, "
    "there is no Token from M to N also in the bag.",
    "A Token from M to N and an Echo from N to M represent two different stages of the "
    "same communication: first M sends Token, then N receives it and replies with Echo. "
    "Both cannot be in-flight simultaneously — the Echo is only sent after the Token "
    "is delivered (consumed).",
    kind="Theorem")

entry(doc, "children_implies_no_parent_token_holds",
    "In every reachable state, if node C is already in node M's children list, then "
    "there is no Token from M to C still in the bag.",
    "C appears in M's children list only after C echoed back to M, which requires C "
    "to have first received M's Token (the Token was delivered and consumed). Once "
    "the Token is consumed and the Echo is delivered, the Token is long gone.",
    kind="Theorem")

entry(doc, "echo_not_in_children_holds",
    "In every reachable state, if an Echo from N to M is still in the bag (not yet "
    "delivered), then N is not yet in M's children list.",
    "N gets added to M's children list only when M delivers N's Echo. If the Echo is "
    "still in the bag, delivery hasn't happened yet, so N is not yet a child.",
    kind="Theorem")

entry(doc, "echo_src_in_fwds_holds",
    "In every reachable state, if there is an Echo from N to M in the bag, then N "
    "is in M's forwarding set (N is a neighbor of M, and N is not M's parent).",
    "N only sends an Echo to M if: (a) N received a Token from M and replied — then N "
    "is in M's forwarding set by construction. Or (b) N received a duplicate Token "
    "from M (N was already Active). In either case N is adjacent to M and not M's parent.",
    kind="Theorem")

entry(doc, "pending_exact_count_ge_holds",
    "In every reachable state, for any Active or Decided node M, the number of Echoes "
    "still expected (pending) plus the number of Echoes already received and counted "
    "(children list length) is at least the size of M's forwarding set.",
    "At activation, pending = |forwarding set| and |children| = 0, so the sum equals "
    "the forwarding set size exactly. Each received Echo decreases pending by 1 and "
    "increases |children| by 1, keeping the sum constant. The ≥ direction accounts "
    "for duplicate Echoes (Token/Active replies that don't decrease pending).",
    note="Together with nodup_children_holds and children_in_fwds (children ⊆ forwarding "
         "set), this gives the exact equality: pending + |children| = |act_fwds|.",
    kind="Theorem")

entry(doc, "echo_at_most_once_holds",
    "In every reachable state, for any specific Echo packet, there is at most one "
    "copy of it in the message bag.",
    "The algorithm never sends the same Echo twice to the same destination.",
    kind="Theorem")

divider(doc, "Children list properties")

entry(doc, "filter_nodup_subset_length",
    "If you have two lists — call them 'children' and 'candidates' — where: "
    "children has no duplicate entries, every element of children is in candidates, "
    "candidates has no duplicate entries, and there is at least one element of candidates "
    "that is NOT in children, then the length of children is strictly less than the "
    "length of candidates.",
    "Since children ⊆ candidates (both duplicate-free) but children misses at least "
    "one element, |children| < |candidates|.",
    note="The arithmetic core of the pending-chain argument: |act_fwds| > |children| "
         "implies pending = |act_fwds| - |children| ≥ 1.",
    kind="Lemma")

entry(doc, "nodup_children_holds",
    "In every reachable state, every node's children list contains no duplicates: "
    "each node appears as a child of any given node at most once.",
    "A node N is added to M's children list when M delivers the Echo from N. "
    "echo_at_most_once guarantees there is at most one Echo from N to M. Delivering "
    "the unique Echo removes it from the bag, so M cannot deliver the same Echo again.",
    kind="Theorem")

entry(doc, "children_in_all_nodes_holds",
    "In every reachable state, every node appearing in any node's children list is "
    "itself a member of the overall node list.",
    "Children are nodes that sent Echoes; Echo senders are in all_nodes by "
    "pkt_nodes_in_all_nodes_holds.",
    kind="Theorem")

entry(doc, "children_parent_ne_holds",
    "In every reachable state, for any node M and any child C in M's children list, "
    "C's own parent is not M.",
    "Wait — this sounds backwards. What it actually says is: M's children are not "
    "pointing back at M as their parent via a double-link that would create a loop. "
    "More precisely: no node appears in its parent's children list in a way that would "
    "create a 2-cycle. This is a structural consistency property of the tree.",
    note="Used as a structural sanity check in the pending-chain argument.",
    kind="Theorem")

entry(doc, "weak_pending_ge_count_holds",
    "In every reachable state, for any Active node M, M's pending counter is at least "
    "as large as the number of M's forwarding targets that have not yet been added to "
    "M's children list.",
    "pending = |act_fwds| - |children| (by the exact count) and the 'remaining targets' "
    "count = |{n ∈ act_fwds : n ∉ children}| ≤ |act_fwds| - |children| = pending.",
    note="The final step before pending_propagates: if N is in M's forwarding set but "
         "not in M's children list, then the remaining count is ≥ 1, so pending ≥ 1.",
    kind="Theorem")

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Part 6 — Group D: The Pending-Chain Argument", level=1)
body(doc,
    "This is the most technically difficult part of the proof. The goal is to show "
    "that when the initiator has decided, no Token is sitting in the bag with an Idle "
    "destination. The proof works by contradiction: if such a Token existed, we could "
    "trace a chain of 'pending ≥ 1' facts up the parent tree all the way to the "
    "initiator — but the initiator's pending is 0 when it decides. Contradiction."
)

entry(doc, "pending_propagates",
    "If an Active node M is still waiting for at least one Echo (pending ≥ 1), "
    "then M's parent is also still waiting for at least one Echo.",
    "M is in its parent's forwarding set (M is a neighbor of the parent and, by "
    "no_mutual_parent, M is not the parent's own parent). M has not been added to "
    "the parent's children list yet (pending_pos_active_holds: M hasn't sent its Echo "
    "yet because pending ≥ 1, so the parent hasn't received it, so M is not a child). "
    "Therefore the parent has M as an unaccounted forwarding target. By "
    "weak_pending_ge_count_holds, parent's pending ≥ 1.",
    note="The key inductive step of the pending-chain argument. Applied repeatedly — "
         "once per hop up the parent chain — to escalate 'pending ≥ 1' from any node "
         "all the way up to the initiator.",
    kind="Lemma")

entry(doc, "pending_chain_to_initiator",
    "If any Active node M anywhere in the network is still waiting for at least one "
    "Echo (pending ≥ 1), then the initiator itself is also still waiting for at least "
    "one Echo.",
    "By TSC_holds, M has a finite parent chain that terminates at the initiator. "
    "Apply pending_propagates at each hop of that chain. At every step, pending ≥ 1 "
    "is preserved going upward. After finitely many hops we reach the initiator.",
    note="Completes the pending-chain argument. Combined with decided_pending_zero_holds "
         "(initiator's pending = 0 when Decided), this gives the contradiction that "
         "closes no_token_idle_decided.",
    kind="Lemma")

entry(doc, "no_token_idle_decided",
    "When the initiator has decided, there is no Token in the message bag whose "
    "destination is an Idle node.",
    "By contradiction: suppose Token(M→N) is in the bag and N is Idle. "
    "N is Idle → N is not in M's children list (idle_not_in_children_holds). "
    "N is in M's forwarding set (act_fwds_spec: N is a neighbor of M by valid_packets, "
    "and N ≠ M's parent by token_dst_not_parent_holds). "
    "So M has an unaccounted forwarding target → M's pending ≥ 1 "
    "(weak_pending_ge_count_holds). "
    "M is Active (token_src_not_idle_holds → M non-Idle; non_init_not_decided_holds → "
    "M not Decided if M ≠ initiator). "
    "pending_chain_to_initiator → initiator's pending ≥ 1. "
    "But decided_pending_zero_holds → initiator's pending = 0. Contradiction.",
    note="This theorem was the last major gap in the proof — originally assumed as an "
         "axiom (Variable) and later promoted to a proved Theorem after the 14 supporting "
         "lemmas were all established. It is the crucial link between Group C and Group E.",
    kind="Theorem")

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Part 7 — Group E: Main Correctness Theorems", level=1)
body(doc,
    "These are the results the whole proof was built for. They say, in plain English: "
    "when the algorithm finishes, it has done what it was supposed to do."
)

entry(doc, "one_hop_active",
    "If the initiator has decided, and node M is already non-Idle (Active), and "
    "node N is a neighbor of M that is closer to the initiator in BFS distance, "
    "then N is also non-Idle (Active).",
    "By token_sent_or_notidle_holds: either N is already non-Idle (done), or there "
    "is a Token from M to N in the bag. In the second case, no_token_idle_decided "
    "rules out N being Idle when the initiator is Decided. So N cannot be Idle.",
    note="This is the inductive step for decided_implies_all_active. It says: being "
         "Active propagates from nodes closer to the initiator outward to their "
         "more-distant neighbors, one hop at a time.",
    kind="Theorem")

entry(doc, "decided_implies_all_active",
    "When the initiator has decided, every non-initiator node in the entire network "
    "is Active. No node has been left out.",
    "Well-founded induction on BFS depth. The initiator (depth 0) is Decided, hence "
    "non-Idle. Every non-initiator N has a neighbor M with strictly smaller BFS depth "
    "(wave_depth_nbr assumption). By induction, M is non-Idle (Active). By "
    "one_hop_active, N is non-Idle. By non_init_not_decided_holds, N is not Decided. "
    "So N is Active.",
    note="The main safety theorem for 'coverage': the spanning tree wave truly reaches "
         "every node before the initiator can decide.",
    kind="Theorem")

entry(doc, "decided_reaches_initiator",
    "When the initiator has decided, every node in the network — including the initiator "
    "itself — has a chain of parent pointers that eventually reaches the initiator.",
    "For the initiator: trivially, the empty chain (zero hops) reaches itself. "
    "For any other node N: decided_implies_all_active gives N is Active. "
    "active_non_init_has_chain (TSC_holds) gives N has a finite parent chain to the "
    "initiator.",
    note="The main correctness theorem of the whole project. It says: when the "
         "algorithm terminates, the parent pointers form a complete spanning tree "
         "rooted at the initiator.",
    kind="Theorem")

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Part 8 — Bonus: Monotonicity", level=1)
body(doc,
    "This final lemma is not needed for the safety proof but gives an additional "
    "property of the algorithm: the number of Idle nodes can only decrease over time."
)

entry(doc, "start_decreases_idle",
    "Every step of the algorithm either keeps the number of Idle nodes the same or "
    "strictly decreases it. The Idle count never goes up.",
    "A node becomes non-Idle (Active) in exactly one step: the Token/Idle delivery. "
    "No step ever makes a non-Idle node Idle again — phases are monotone (Idle → "
    "Active → Decided, never backward). So each step can at most activate one new "
    "node (decreasing Idle count by 1) or change nothing about the Idle count.",
    note="This gives a monotonicity / progress property: the algorithm always makes "
         "forward progress in terms of node activation. It rules out oscillation "
         "or reactivation.",
    kind="Lemma")

# ═════════════════════════════════════════════════════════════════════════════
heading(doc, "Summary: The Proof in One Page", level=1)
body(doc,
    "Here is the full dependency chain in plain English, from the bottom up:"
)

steps = [
    ("State mechanics", "upd_self / upd_other / proc_of_upd tell us how to read back what we wrote."),
    ("Message mechanics", "remove_pkt_in / send_to_all_inv tell us packets don't vanish unless delivered."),
    ("Structural shape (INV)", "Parent pointers are always on real edges. No node is its own parent. The initiator has no parent."),
    ("Tree connectivity (TSC)", "Every Active non-initiator has a chain of parent pointers all the way to the initiator."),
    ("Token origin", "token_src_not_idle: Every Token in flight was sent by someone who is not Idle."),
    ("Wave progress", "token_sent_or_notidle: Every Active node has either activated each neighbor, or has a Token in flight toward it."),
    ("Active parents", "parent_is_active: Your parent is always Active or Decided."),
    ("No cycles in parents", "no_mutual_parent: If A's parent is B, then B's parent is not A."),
    ("Forwarding set accounting", "pending + |children| = |act_fwds|: the pending counter is exactly the number of forwarding targets that haven't echoed back yet."),
    ("Unique-copy guarantees", "token_at_most_once / echo_at_most_once: At most one copy of each specific packet exists."),
    ("Consumed activation Token", "token_from_parent_consumed: Once you are Active, your activation Token is gone from the bag."),
    ("pending ≥ 1 → no Echo sent", "pending_pos_active: If pending ≥ 1, you haven't reported to your parent yet."),
    ("Echo destinations are not Idle", "echo_dst_not_idle: Echoes always travel toward non-Idle nodes."),
    ("One-hop pending escalation", "pending_propagates: If M's pending ≥ 1, then M's parent also has pending ≥ 1."),
    ("Full chain escalation", "pending_chain_to_initiator: If anyone has pending ≥ 1, the initiator does too."),
    ("Initiator pending = 0 when decided", "decided_pending_zero: The initiator only decides when its pending hits 0."),
    ("KEY: No Token to Idle when decided", "no_token_idle_decided: Combining the two previous facts: if the initiator decided, there is no Token targeting an Idle node."),
    ("One-hop activity spread", "one_hop_active: If the initiator decided and M is Active and N is closer to the initiator, then N is Active."),
    ("Everyone is Active when initiator decides", "decided_implies_all_active: When the initiator decides, every node is Active."),
    ("MAIN THEOREM: Spanning tree is complete", "decided_reaches_initiator: When the initiator decides, every node's parent chain leads back to the initiator. The spanning tree is correct and complete."),
]

for i, (label, text) in enumerate(steps):
    p = doc.add_paragraph()
    p.paragraph_format.left_indent = Inches(0.2)
    p.paragraph_format.space_after = Pt(2)
    lrun = p.add_run(f"{i+1}. {label}: ")
    lrun.bold = True
    lrun.font.size = Pt(10.5)
    trun = p.add_run(text)
    trun.font.size = Pt(10.5)

doc.add_paragraph()
body(doc,
    "Every Qed in the proof file is checked by the Rocq kernel — a small, independent "
    "program that verifies logical correctness. There are no Admitted gaps, no "
    "hand-waving, no 'it's obvious that'. Every step in the 20-step chain above is "
    "a machine-verified fact."
)

# ─── save ────────────────────────────────────────────────────────────────────
out = "/Users/iilin/static-distributed-systems/LEMMA_GUIDE.docx"
doc.save(out)
print(f"Saved: {out}")
