import networkx as nx
import matplotlib.pyplot as plt

# Define color map for symbolic elements
color_map = {
    '0': 'red',
    '1': 'blue',
    'x': 'green',
    '(': 'black',
    ')': 'black',
    '[': 'black',
    ']': 'black',
    '{': 'black',
    '}': 'black'
}

# Assign internal structure (optional quark-like substructure)
quark_map = {
    '0': [('red', 'up'), ('green', 'up'), ('blue', 'down')],
    'x': [('red', 'strange'), ('green', 'down'), ('blue', 'charm')]
}

def parse_structure(expr):
    G = nx.DiGraph()
    stack = []
    node_id = 0

    def new_node(label):
        nonlocal node_id
        name = f"n{node_id}"
        G.add_node(name, label=label)
        node_id += 1
        return name

    for c in expr:
        if c in "([{":
            n = new_node(c)
            if stack:
                G.add_edge(stack[-1], n)
            stack.append(n)
        elif c in ")]}":
            if stack:
                stack.pop()
        elif c.strip():  # ignore whitespace
            n = new_node(c)
            if stack:
                G.add_edge(stack[-1], n)

    return G

def draw_structure(G, title="Symbolic Field Tree"):
    pos = nx.spring_layout(G, seed=42)
    labels = nx.get_node_attributes(G, 'label')
    
    colors = []
    for node in G.nodes():
        label = labels[node]
        colors.append(color_map.get(label, 'gray'))  # default gray for unknowns

    nx.draw(G, pos, labels=labels, node_color=colors,
            with_labels=True, node_size=900, font_color='white', arrows=True)
    plt.title(title)
    plt.show()

def print_quark_structure(G):
    labels = nx.get_node_attributes(G, 'label')
    for node, label in labels.items():
        if label in quark_map:
            print(f"Node {label}: quark structure = {quark_map[label]}")

# Example usage
if __name__ == "__main__":
    expression = "(0)(0)[0 0]{x0}"
    G = parse_structure(expression)
    draw_structure(G)
    print_quark_structure(G)
