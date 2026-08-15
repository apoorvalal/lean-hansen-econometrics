document.addEventListener("DOMContentLoaded", () => {
  const host = document.getElementById("dependency-graph");
  const dataElement = document.getElementById("dependency-data");
  if (!host || !dataElement || !window.d3) return;

  const data = JSON.parse(dataElement.textContent);
  const canvas = d3.select("#graph-canvas");
  const chapterSelect = document.getElementById("graph-chapter");
  const overviewButton = document.getElementById("graph-overview");
  const resetButton = document.getElementById("graph-reset");
  const status = document.getElementById("graph-status");
  const width = document.getElementById("graph-canvas").clientWidth || 1100;
  const height = 680;
  let simulation = null;
  let zoom = null;
  let currentFit = null;

  for (const chapter of data.chapters) {
    const option = document.createElement("option");
    option.value = String(chapter);
    option.textContent = `Chapter ${chapter}`;
    chapterSelect.appendChild(option);
  }

  const defineArrow = () => {
    const definitions = canvas.append("defs");
    definitions
      .append("marker")
      .attr("id", "dependency-arrow")
      .attr("viewBox", "0 -5 10 10")
      .attr("refX", 10)
      .attr("refY", 0)
      .attr("markerWidth", 11)
      .attr("markerHeight", 11)
      .attr("markerUnits", "userSpaceOnUse")
      .attr("orient", "auto")
      .append("path")
      .attr("d", "M0,-4L10,0L0,4")
      .attr("fill", "#a36b16");
  };

  const clear = () => {
    if (simulation) simulation.stop();
    canvas.selectAll("*").remove();
    defineArrow();
  };

  const linkGeometry = (link, targetRadius) => {
    const dx = link.target.x - link.source.x;
    const dy = link.target.y - link.source.y;
    const length = Math.hypot(dx, dy) || 1;
    return {
      x1: link.source.x,
      y1: link.source.y,
      x2: link.target.x - (dx / length) * (targetRadius + 3),
      y2: link.target.y - (dy / length) * (targetRadius + 3),
    };
  };

  const enableZoom = (root, labels) => {
    zoom = d3.zoom().scaleExtent([0.08, 5]).on("zoom", (event) => {
      root.attr("transform", event.transform);
      if (labels) {
        labels.style("display", (node) =>
          event.transform.k >= 1.5 || node.showLabel ? null : "none"
        );
      }
    });
    canvas.call(zoom);
  };

  const fit = (root, nodes) => {
    if (!nodes.length || !zoom) return;
    const xs = nodes.map((node) => node.x).filter(Number.isFinite);
    const ys = nodes.map((node) => node.y).filter(Number.isFinite);
    if (!xs.length) return;
    const padding = 55;
    const minX = Math.min(...xs);
    const maxX = Math.max(...xs);
    const minY = Math.min(...ys);
    const maxY = Math.max(...ys);
    const graphWidth = Math.max(maxX - minX, 1);
    const graphHeight = Math.max(maxY - minY, 1);
    const scale = Math.min(
      2,
      (width - 2 * padding) / graphWidth,
      (height - 2 * padding) / graphHeight
    );
    const tx = width / 2 - scale * (minX + maxX) / 2;
    const ty = height / 2 - scale * (minY + maxY) / 2;
    canvas
      .transition()
      .duration(350)
      .call(zoom.transform, d3.zoomIdentity.translate(tx, ty).scale(scale));
  };

  const enableDrag = (selection, root) => {
    selection.call(
      d3
        .drag()
        .container(() => root.node())
        .clickDistance(4)
        .on("start", (event, node) => {
          if (!event.active) simulation.alphaTarget(0.25).restart();
          node.fx = node.x;
          node.fy = node.y;
          event.sourceEvent.stopPropagation();
        })
        .on("drag", (event, node) => {
          node.fx = event.x;
          node.fy = event.y;
        })
        .on("end", (event) => {
          if (!event.active) simulation.alphaTarget(0);
        })
    );
    selection.on("dblclick", (event, node) => {
      event.stopPropagation();
      node.fx = null;
      node.fy = null;
      simulation.alpha(0.25).restart();
    });
  };

  const drawOverview = () => {
    clear();
    chapterSelect.value = "";
    const importantCounts = new Map();
    for (const node of data.nodes) {
      if (node.important && node.chapter !== null) {
        importantCounts.set(node.chapter, (importantCounts.get(node.chapter) || 0) + 1);
      }
    }
    const nodes = data.chapters.map((chapter) => ({
      id: chapter,
      count: importantCounts.get(chapter) || 0,
    }));
    const edgeCounts = new Map();
    for (const [fromIndex, toIndex] of data.edges) {
      const from = data.nodes[fromIndex].chapter;
      const to = data.nodes[toIndex].chapter;
      if (from === null || to === null || from === to) continue;
      const key = `${from}|${to}`;
      edgeCounts.set(key, (edgeCounts.get(key) || 0) + 1);
    }
    const links = [...edgeCounts.entries()].map(([key, count]) => {
      const [source, target] = key.split("|").map(Number);
      return { source, target, count };
    });
    const root = canvas.append("g");
    const link = root
      .append("g")
      .selectAll("line")
      .data(links)
      .join("line")
      .attr("stroke", "#b7a482")
      .attr("stroke-opacity", 0.55)
      .attr("stroke-width", (item) => Math.min(1 + Math.log2(1 + item.count), 6))
      .attr("marker-end", "url(#dependency-arrow)");
    const node = root
      .append("g")
      .selectAll("g")
      .data(nodes)
      .join("g")
      .attr("tabindex", 0)
      .style("cursor", "pointer")
      .on("click", (_event, item) => drawChapter(item.id))
      .on("keydown", (event, item) => {
        if (event.key === "Enter" || event.key === " ") drawChapter(item.id);
      });
    node
      .append("circle")
      .attr("r", (item) => 15 + Math.sqrt(item.count) * 1.7)
      .attr("fill", "#ffffff")
      .attr("stroke", "#355b78")
      .attr("stroke-width", 2);
    node
      .append("text")
      .text((item) => `Ch. ${item.id}`)
      .attr("text-anchor", "middle")
      .attr("dy", "0.15em")
      .style("font-size", "0.72rem")
      .style("font-weight", 600)
      .style("fill", "#263238");
    node
      .append("text")
      .text((item) => `${item.count} results`)
      .attr("text-anchor", "middle")
      .attr("dy", "1.45em")
      .style("font-size", "0.55rem")
      .style("fill", "#607078");
    node.append("title").text((item) => `Chapter ${item.id}: ${item.count} important declarations`);
    enableDrag(node, root);
    enableZoom(root, null);
    currentFit = () => fit(root, nodes);
    simulation = d3
      .forceSimulation(nodes)
      .force("link", d3.forceLink(links).id((item) => item.id).distance(190))
      .force("charge", d3.forceManyBody().strength(-950))
      .force("center", d3.forceCenter(width / 2, height / 2))
      .force("collision", d3.forceCollide().radius((item) => 32 + Math.sqrt(item.count)))
      .on("tick", () => {
        link
          .attr("x1", (item) => (item.geometry = linkGeometry(item, 15 + Math.sqrt(item.target.count) * 1.7)).x1)
          .attr("y1", (item) => item.geometry.y1)
          .attr("x2", (item) => item.geometry.x2)
          .attr("y2", (item) => item.geometry.y2);
        node.attr("transform", (item) => `translate(${item.x},${item.y})`);
      })
      .on("end", currentFit);
    status.textContent = `${nodes.length} chapters, ${links.length} cross-chapter links`;
  };

  const drawChapter = (chapter) => {
    clear();
    chapterSelect.value = String(chapter);
    const primary = new Set();
    data.nodes.forEach((node, index) => {
      if (node.chapter === chapter) primary.add(index);
    });
    const visible = new Set(primary);
    for (const [from, to] of data.edges) {
      if (primary.has(to) && data.nodes[to].important) visible.add(from);
    }
    const oldToNew = new Map();
    const nodes = [];
    [...visible].sort((a, b) => a - b).forEach((oldIndex) => {
      oldToNew.set(oldIndex, nodes.length);
      nodes.push({ ...data.nodes[oldIndex], oldIndex });
    });
    const links = data.edges
      .filter(([from, to]) => visible.has(from) && visible.has(to))
      .map(([from, to]) => ({ source: oldToNew.get(from), target: oldToNew.get(to) }));
    const degree = new Array(nodes.length).fill(0);
    for (const link of links) {
      degree[link.source] += 1;
      degree[link.target] += 1;
    }
    const degreeCut = [...degree].sort((a, b) => b - a)[Math.min(29, degree.length - 1)] || 0;
    nodes.forEach((node, index) => {
      node.showLabel = node.important || degree[index] >= degreeCut;
    });
    const root = canvas.append("g");
    const link = root
      .append("g")
      .selectAll("line")
      .data(links)
      .join("line")
      .attr("stroke", "#b7a482")
      .attr("stroke-opacity", 0.45)
      .attr("stroke-width", 1)
      .attr("marker-end", "url(#dependency-arrow)");
    const node = root
      .append("g")
      .selectAll("g")
      .data(nodes)
      .join("g")
      .attr("tabindex", 0)
      .style("cursor", "pointer")
      .on("click", (_event, item) => {
        location.href = item.page;
      })
      .on("keydown", (event, item) => {
        if (event.key === "Enter" || event.key === " ") location.href = item.page;
      });
    node
      .append("circle")
      .attr("r", (item) => (item.important ? 7 : 4.5))
      .attr("fill", (item) => (item.important ? "#355b78" : "#9aa7ad"))
      .attr("stroke", (item) => (item.chapter === chapter ? "#ffffff" : "#a36b16"))
      .attr("stroke-width", (item) => (item.chapter === chapter ? 1 : 2));
    const labels = node
      .append("text")
      .text((item) => item.short)
      .attr("dx", 9)
      .attr("dy", "0.32em")
      .style("font-family", "ui-monospace, SFMono-Regular, Menlo, monospace")
      .style("font-size", "0.59rem")
      .style("fill", "#34434a")
      .attr("paint-order", "stroke")
      .attr("stroke", "#fcfdfd")
      .attr("stroke-width", 3)
      .style("display", (item) => (item.showLabel ? null : "none"));
    node.append("title").text((item) => `${item.kind} ${item.name}\n${item.doc}`);
    enableDrag(node, root);
    enableZoom(root, labels);
    currentFit = () => fit(root, nodes);
    simulation = d3
      .forceSimulation(nodes)
      .force("link", d3.forceLink(links).distance(90))
      .force("charge", d3.forceManyBody().strength(-190))
      .force("center", d3.forceCenter(width / 2, height / 2))
      .force("x", d3.forceX(width / 2).strength(0.06))
      .force("y", d3.forceY(height / 2).strength(0.06))
      .force("collision", d3.forceCollide().radius((item) => (item.important ? 18 : 12)))
      .on("tick", () => {
        link
          .attr("x1", (item) => (item.geometry = linkGeometry(item, item.target.important ? 7 : 4.5)).x1)
          .attr("y1", (item) => item.geometry.y1)
          .attr("x2", (item) => item.geometry.x2)
          .attr("y2", (item) => item.geometry.y2);
        node.attr("transform", (item) => `translate(${item.x},${item.y})`);
      })
      .on("end", currentFit);
    const important = nodes.filter((item) => item.important && item.chapter === chapter).length;
    status.textContent = `Chapter ${chapter}: ${important} important results, ${nodes.length - important} direct dependencies`;
    history.replaceState(null, "", `?chapter=${chapter}`);
  };

  overviewButton.addEventListener("click", () => {
    history.replaceState(null, "", location.pathname);
    drawOverview();
  });
  chapterSelect.addEventListener("change", () => {
    if (chapterSelect.value) drawChapter(Number(chapterSelect.value));
    else drawOverview();
  });
  resetButton.addEventListener("click", () => currentFit && currentFit());

  const requested = Number(new URLSearchParams(location.search).get("chapter"));
  if (data.chapters.includes(requested)) drawChapter(requested);
  else drawOverview();
});

