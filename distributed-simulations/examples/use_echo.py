"""Minimal use of the public Rocq-generated Echo API."""

from distributed_simulations.echo import EchoNetwork, run_echo


network = EchoNetwork.from_edges(
    (("A", "B"), ("B", "C"), ("C", "A")),
    initiator="A",
)
result = run_echo(network, scheduler="fifo")

print("completed:", result.completed)
print("verified:", result.verified)
print("parents:", dict(result.parents))
print("tree edges:", result.tree_edges)
print("C to initiator:", result.path_to_initiator("C"))
