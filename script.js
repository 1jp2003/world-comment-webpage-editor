"use strict";

/*
 * World Comment Editor
 *
 * File layout of one comment record (all numbers big-endian), offsets from the record start.
 * This mirrors CommentEntry.writeBuffer / the CommentEntry(...) constructor in the mod:
 *
 *    0        deleted      boolean
 *    1        uplinkSent   boolean
 *    2-3      unused
 *    4-7      like         int
 *    8-15     marker       "====ZBX="
 *   16-23     id           long
 *   24-31     timestamp    long (ms since 1970)
 *   32-39     location     packed long: x = top 26 bits, z = next 26, y = low 12 (two's complement)
 *   40-55     initiator    UUID
 *   56-       name         varint length + UTF-8
 *             messageType  int
 *             message      varint length + UTF-8
 *             image url    varint length + UTF-8
 *             thumb url    varint length + UTF-8
 *             padding      1-16 zero bytes, up to the next multiple of 16
 *
 * The dimension is NOT stored in the record. It is the folder name: region/<namespace>+<path>/.
 * A comment belongs in file r.<x>.<z>.bin where x = blockX >> 6 and z = blockZ >> 6.
 */

const MARKER = [0x3d, 0x3d, 0x3d, 0x3d, 0x5a, 0x42, 0x58, 0x3d]; // "====ZBX="
const REGION_SHIFT = 6; // 16 blocks per chunk * 4 chunks per region = 64 = 2^6
const LOCAL_IMAGE_PREFIX = "file://worldcomment/";
const TYPE_NAMES = ["Great", "Good", "Advice", "NoGood", "ToDo", "Warn", "Tip", "Memo"];
const TYPE_COLORS = ["#8BC34A", "#CDDC39", "#FFEB3B", "#FF9800", "#607D8B", "#FFC107", "#03A9F4", "#009888"];
const LIMITS = { x: [-33554432, 33554431], y: [-2048, 2047], z: [-33554432, 33554431] };

const utf8 = new TextDecoder("utf-8", { fatal: true });

// ---------- DOM ----------
const folderInput = document.getElementById("folderInput");
const fileInput = document.getElementById("fileInput");
const statusEl = document.getElementById("status");
const summaryEl = document.getElementById("summary");
const toolsEl = document.getElementById("tools");
const filterInput = document.getElementById("filterInput");
const loadRemoteInput = document.getElementById("loadRemoteInput");
const showDeletedInput = document.getElementById("showDeletedInput");
const shiftScopeEl = document.getElementById("shiftScope");
const sortSelect = document.getElementById("sortSelect");
const dateFrom = document.getElementById("dateFrom");
const dateTo = document.getElementById("dateTo");
const countLabel = document.getElementById("countLabel");
const sectionsEl = document.getElementById("sections");
const saveBtn = document.getElementById("saveBtn");
const selectionLabel = document.getElementById("selectionLabel");
const applySelectedBtn = document.getElementById("applySelectedBtn");
const clearSelectionBtn = document.getElementById("clearSelectionBtn");

// ---------- State ----------
let comments = [];        // every parsed comment, in load order
let shown = [];           // comments passing the current filter (and the "show deleted" toggle)
let headerBoxes = [];     // per-section "select all" checkboxes of the current render
let openSections = new Map(); // dimDir -> is its <details> section open? (survives re-rendering)
let loadedPaths = new Set(); // "dimDir/r.X.Z.bin" of every file that was loaded
let imageFiles = new Map();  // file name -> File (from the image/ folder)
let thumbUrls = new Map();   // file name -> object URL, created on demand
let loadError = null;

// ---------- Low-level readers ----------
function readVarInt(bytes, offset) {
    let value = 0, shift = 0, pos = offset;
    while (true) {
        if (pos >= bytes.length) throw new Error("ran past the end of the file while reading a length");
        const b = bytes[pos++];
        value |= (b & 0x7f) << shift;
        if ((b & 0x80) === 0) break;
        shift += 7;
        if (shift > 28) throw new Error("a length field is too long to be valid");
    }
    return { value, next: pos };
}

function readUtf(bytes, offset) {
    const { value: length, next } = readVarInt(bytes, offset);
    if (next + length > bytes.length) throw new Error("a text field runs past the end of the file");
    const str = utf8.decode(bytes.subarray(next, next + length)); // throws on invalid UTF-8
    return { str, next: next + length };
}

function signed(value, bits) {
    return value >= (1n << BigInt(bits - 1)) ? value - (1n << BigInt(bits)) : value;
}

function unpackPos(packed) {
    return {
        x: Number(signed((packed >> 38n) & 0x3FFFFFFn, 26)),
        z: Number(signed((packed >> 12n) & 0x3FFFFFFn, 26)),
        y: Number(signed(packed & 0xFFFn, 12)),
    };
}

function packPos(x, y, z) {
    // Mask every part first so negative numbers don't spill into neighbouring fields.
    return ((BigInt(x) & 0x3FFFFFFn) << 38n) | ((BigInt(z) & 0x3FFFFFFn) << 12n) | (BigInt(y) & 0xFFFn);
}

function uuidToString(bytes) {
    const h = Array.from(bytes, b => b.toString(16).padStart(2, "0")).join("");
    return `${h.slice(0, 8)}-${h.slice(8, 12)}-${h.slice(12, 16)}-${h.slice(16, 20)}-${h.slice(20)}`;
}

const regionOf = (x, z) => ({ rx: x >> REGION_SHIFT, rz: z >> REGION_SHIFT });

// ---------- Parsing ----------
/** Parse one region file. Never throws: returns what it could read plus an error message. */
function parseRegionFile(bytes, source) {
    const out = [];
    const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    let i = 0;
    try {
        while (i < bytes.length) {
            if (i + 56 > bytes.length) throw new Error("the file ends in the middle of a comment");
            for (let k = 0; k < 8; k++) {
                if (bytes[i + 8 + k] !== MARKER[k]) {
                    throw new Error("the ====ZBX= marker is not where expected (file damaged, hand-edited, or a different format)");
                }
            }
            const pos = unpackPos(dv.getBigUint64(i + 32));
            let j = i + 56;
            const name = readUtf(bytes, j); j = name.next;
            if (j + 4 > bytes.length) throw new Error("the file ends in the middle of a comment");
            const messageType = dv.getInt32(j); j += 4;
            const message = readUtf(bytes, j); j = message.next;
            const url = readUtf(bytes, j); j = url.next;
            const thumb = readUtf(bytes, j); j = thumb.next;
            j += 16 - (j % 16); // padding is always 1..16 bytes
            if (j > bytes.length) throw new Error("the padding runs past the end of the file");

            out.push({
                source,
                raw: bytes.slice(i, j),              // exact bytes of this comment, copied
                deleted: bytes[i] !== 0,
                uplinkSent: bytes[i + 1] !== 0,
                like: dv.getInt32(i + 4),
                id: dv.getBigInt64(i + 16),
                timestamp: Number(dv.getBigInt64(i + 24)),
                x: pos.x, y: pos.y, z: pos.z,
                newX: pos.x, newY: pos.y, newZ: pos.z,
                uuid: uuidToString(bytes.subarray(i + 40, i + 56)),
                name: name.str,
                messageType,
                message: message.str,
                url: url.str,
                thumb: thumb.str,
            });
            i = j;
        }
    } catch (err) {
        return { comments: out, error: `${source.path}\n  comment #${out.length + 1} at byte ${i}: ${err.message}` };
    }
    return { comments: out, error: null };
}

function describeSource(file) {
    const path = file.webkitRelativePath || file.name;
    const parts = path.split("/");
    const m = /^r\.(-?\d+)\.(-?\d+)\.bin$/.exec(parts[parts.length - 1]);
    if (!m) return null;
    const dimDir = parts.length >= 2 ? parts[parts.length - 2] : "unknown";
    return {
        path,
        dimDir,
        dimLabel: dimDir === "unknown" ? "(unknown dimension)" : dimDir.replace("+", ":"),
        rx: Number(m[1]),
        rz: Number(m[2]),
        fileName: parts[parts.length - 1],
    };
}

// ---------- Loading ----------
async function handleFiles(fileList) {
    const files = Array.from(fileList);
    if (!files.length) return;

    statusEl.className = "status";
    statusEl.textContent = "Reading files...";
    comments = [];
    loadedPaths = new Set();
    openSections = new Map();
    loadError = null;
    for (const url of thumbUrls.values()) URL.revokeObjectURL(url);
    thumbUrls = new Map();
    imageFiles = new Map();

    const regionFiles = [];
    for (const f of files) {
        const path = f.webkitRelativePath || f.name;
        const parts = path.split("/");
        if (parts.length >= 2 && parts[parts.length - 2] === "image") {
            imageFiles.set(parts[parts.length - 1], f);
            continue;
        }
        const src = describeSource(f);
        if (src) regionFiles.push({ file: f, src });
    }
    regionFiles.sort((a, b) => a.src.path.localeCompare(b.src.path, undefined, { numeric: true }));

    const errors = [];
    for (const { file, src } of regionFiles) {
        const bytes = new Uint8Array(await file.arrayBuffer());
        const result = parseRegionFile(bytes, src);
        comments.push(...result.comments);
        loadedPaths.add(`${src.dimDir}/${src.fileName}`);
        if (result.error) errors.push(result.error);
    }
    comments.forEach((c, n) => {
        c.number = n + 1;
        const typeName = TYPE_NAMES[c.messageType - 1] || `type ${c.messageType}`;
        c.searchText = [c.name, c.message, typeName, c.source.dimLabel, c.source.fileName].join("\n").toLowerCase();
    });

    if (!regionFiles.length) {
        statusEl.className = "status error";
        statusEl.textContent = "No r.X.Z.bin files found in that selection.";
        return;
    }
    if (errors.length) {
        loadError = errors.join("\n");
        statusEl.className = "status error";
        statusEl.textContent =
            "Could not fully read these file(s). Saving is disabled so nothing gets lost.\n" + loadError;
    } else {
        statusEl.className = "status ok";
        statusEl.textContent =
            `Read ${regionFiles.length} file(s): ${comments.length} comments, ${imageFiles.size} image file(s).`;
    }

    renderSummary();
    fillShiftScope();
    toolsEl.hidden = false;
    renderTable();
    saveBtn.disabled = !!loadError || comments.length === 0;
}

// ---------- Summary ----------
function renderSummary() {
    const deleted = comments.filter(c => c.deleted).length;
    const authors = new Set(comments.filter(c => !c.deleted && c.name).map(c => c.name));
    const anonymous = comments.filter(c => !c.deleted && !c.name).length;
    const withImage = comments.filter(c => c.url || c.thumb).length;
    const mismatched = comments.filter(c => {
        const r = regionOf(c.x, c.z);
        return r.rx !== c.source.rx || r.rz !== c.source.rz;
    }).length;
    const typeCounts = new Map();
    comments.filter(c => !c.deleted).forEach(c => typeCounts.set(c.messageType, (typeCounts.get(c.messageType) || 0) + 1));
    const dims = new Set(comments.map(c => c.source.dimLabel));

    summaryEl.replaceChildren();
    const line = (...nodes) => {
        const div = document.createElement("div");
        nodes.forEach(n => div.append(n));
        summaryEl.append(div);
    };

    line(`${comments.length} comments (${comments.length - deleted} active, ${deleted} deleted), `
        + `${authors.size} named author(s), ${anonymous} anonymous, ${withImage} with an image. `
        + `Dimensions: ${Array.from(dims).join(", ") || "none"}.`);

    if (comments.length) {
        const xs = comments.map(c => c.x), zs = comments.map(c => c.z);
        line(`Extent: X ${Math.min(...xs)} to ${Math.max(...xs)}, Z ${Math.min(...zs)} to ${Math.max(...zs)}.`);
    }

    const chips = document.createElement("div");
    chips.append("By type: ");
    Array.from(typeCounts.keys()).sort((a, b) => a - b).forEach(t => {
        chips.append(makeTypeChip(t), ` ${typeCounts.get(t)}  `);
    });
    summaryEl.append(chips);

    if (mismatched) {
        const w = document.createElement("div");
        w.className = "warn";
        w.textContent = `${mismatched} comment(s) are stored in a file whose name does not match their position. `
            + `Saving will put each one in the file that matches where it is.`;
        summaryEl.append(w);
    }
    summaryEl.hidden = false;
}

function makeTypeChip(type) {
    const chip = document.createElement("span");
    chip.className = "chip";
    chip.textContent = TYPE_NAMES[type - 1] || `type ${type}`;
    chip.style.background = TYPE_COLORS[type - 1] || "#cfd8dc";
    return chip;
}

// ---------- Dimensions ----------
const COLUMNS = ["", "#", "Image", "User", "Message", "Posted", "Type", "Position", "Will be saved in"];

const DIMENSION_NAMES = {
    "minecraft:overworld": "Overworld",
    "minecraft:the_nether": "Nether",
    "minecraft:the_end": "The End",
};

/** "minecraft+the_nether" -> "Nether (minecraft:the_nether)"; unknown ones show the raw name. */
function dimensionTitle(dimDir) {
    if (dimDir === "unknown") return "Unknown dimension";
    const label = dimDir.replace("+", ":");
    return DIMENSION_NAMES[label] ? `${DIMENSION_NAMES[label]} (${label})` : label;
}

/** Overworld, Nether, End first; other dimensions alphabetically; unknown last. */
function dimensionOrder(dimDir) {
    const label = dimDir.replace("+", ":");
    const fixed = Object.keys(DIMENSION_NAMES).indexOf(label);
    if (fixed !== -1) return [fixed, ""];
    return dimDir === "unknown" ? [99, ""] : [10, dimDir];
}

function sortedDimensions() {
    const dims = new Set(comments.map(c => c.source.dimDir));
    return Array.from(dims).sort((a, b) => {
        const [oa, na] = dimensionOrder(a), [ob, nb] = dimensionOrder(b);
        return oa - ob || na.localeCompare(nb);
    });
}

/** Fill the "shift comments in ..." dropdown with the dimensions that were loaded. */
function fillShiftScope() {
    shiftScopeEl.replaceChildren(new Option("all dimensions", ""));
    for (const dimDir of sortedDimensions()) shiftScopeEl.append(new Option(dimensionTitle(dimDir), dimDir));
}

// ---------- Timeframe: date range filter and sorting ----------
/** Keeps comments posted inside the chosen day range (local time, both ends inclusive). */
function filterByDate(list) {
    // <input type="date"> gives "YYYY-MM-DD", or "" when empty. Building the Date from parts uses local time.
    const dayStart = value => {
        if (!value) return null;
        const [y, m, d] = value.split("-").map(Number);
        return new Date(y, m - 1, d).getTime();
    };
    const from = dayStart(dateFrom.value);
    const toDay = dayStart(dateTo.value);
    if (from === null && toDay === null) return list;
    const to = toDay === null ? null : toDay + 24 * 60 * 60 * 1000; // end of that day (exclusive)
    return list.filter(c => {
        if (!c.timestamp) return false; // no timestamp: can't be placed in a range
        return (from === null || c.timestamp >= from) && (to === null || c.timestamp < to);
    });
}

/** Sorts a copy by post time; JS sort is stable, so ties keep their original order. */
function sortComments(list) {
    if (sortSelect.value === "new") return [...list].sort((a, b) => b.timestamp - a.timestamp);
    if (sortSelect.value === "old") return [...list].sort((a, b) => a.timestamp - b.timestamp);
    return list;
}

// ---------- Table ----------
function renderTable() {
    const needle = filterInput.value.trim().toLowerCase();
    const matching = comments.filter(c => !needle || c.searchText.includes(needle));
    const visible = showDeletedInput.checked ? matching : matching.filter(c => !c.deleted);
    const hiddenDeleted = matching.length - visible.length;
    shown = sortComments(filterByDate(visible));

    // One section per dimension. Group everything first so a dimension whose comments are all
    // filtered out still gets a section (with a note) instead of silently vanishing.
    const groups = new Map();
    for (const dimDir of sortedDimensions()) groups.set(dimDir, { all: [], shown: [] });
    for (const c of comments) groups.get(c.source.dimDir).all.push(c);
    for (const c of shown) groups.get(c.source.dimDir).shown.push(c);

    headerBoxes = [];
    sectionsEl.replaceChildren(...Array.from(groups, ([dimDir, g]) => buildSection(dimDir, g)));

    countLabel.textContent = `Showing ${shown.length} of ${comments.length}`
        + (hiddenDeleted ? ` (${hiddenDeleted} deleted hidden)` : "");
    refreshSelectionUI();
}

// Updates the "N selected" label, the header checkboxes and the selection buttons without re-rendering.
function refreshSelectionUI() {
    const selected = comments.filter(c => c.selected);
    const hidden = selected.filter(c => !shown.includes(c)).length;
    selectionLabel.textContent = `${selected.length} selected`
        + (hidden ? ` (${hidden} hidden by filter)` : "");
    applySelectedBtn.disabled = selected.length === 0;
    clearSelectionBtn.disabled = selected.length === 0;
    for (const { box, shown: list } of headerBoxes) {
        const n = list.filter(c => c.selected).length;
        box.checked = list.length > 0 && n === list.length;
        box.indeterminate = n > 0 && n < list.length;
    }
}

function buildSection(dimDir, group) {
    const details = document.createElement("details");
    details.className = "dimension";
    details.open = openSections.has(dimDir) ? openSections.get(dimDir) : true;
    details.addEventListener("toggle", () => openSections.set(dimDir, details.open));

    const deletedCount = group.all.filter(c => c.deleted).length;
    const summary = document.createElement("summary");
    summary.append(dimensionTitle(dimDir));
    const meta = document.createElement("span");
    meta.className = "meta";
    meta.textContent = `  ${group.shown.length} shown of ${group.all.length}`
        + (deletedCount ? `, ${deletedCount} deleted` : "");
    summary.append(meta);
    details.append(summary);

    if (!group.shown.length) {
        const note = document.createElement("p");
        note.className = "muted dim-empty";
        note.textContent = group.all.length
            ? "No comments to show here (check the filter or date range, or turn on \"Show deleted comments\")."
            : "No comments.";
        details.append(note);
        return details;
    }

    const wrap = document.createElement("div");
    wrap.className = "table-wrap";
    const table = document.createElement("table");
    const headRow = document.createElement("tr");
    for (const name of COLUMNS) {
        const th = document.createElement("th");
        if (name === "") {
            // Header checkbox = select / unselect every comment shown in this section.
            const box = document.createElement("input");
            box.type = "checkbox";
            box.title = "Select all shown in this section";
            box.addEventListener("change", () => {
                group.shown.forEach(c => { c.selected = box.checked; c.checkbox.checked = box.checked; });
                group.shown.forEach(c => c.row.classList.toggle("selected", c.selected));
                refreshSelectionUI();
            });
            headerBoxes.push({ box, shown: group.shown });
            th.append(box);
        } else {
            th.textContent = name;
        }
        headRow.append(th);
    }
    const thead = document.createElement("thead");
    thead.append(headRow);
    const tbody = document.createElement("tbody");
    tbody.append(...group.shown.map(buildRow));
    table.append(thead, tbody);
    wrap.append(table);
    details.append(wrap);
    return details;
}

function cell(content, className) {
    const td = document.createElement("td");
    if (className) td.className = className;
    if (content instanceof Node) td.append(content); else td.textContent = content;
    return td;
}

function thumbCell(c) {
    const td = document.createElement("td");
    const thumbName = c.thumb.startsWith(LOCAL_IMAGE_PREFIX) ? c.thumb.slice(LOCAL_IMAGE_PREFIX.length) : null;
    const fullName = c.url.startsWith(LOCAL_IMAGE_PREFIX) ? c.url.slice(LOCAL_IMAGE_PREFIX.length) : null;
    const thumbFile = thumbName && imageFiles.get(thumbName);
    if (thumbFile) {
        const img = document.createElement("img");
        img.className = "thumb";
        img.loading = "lazy";
        img.alt = "thumbnail";
        img.src = objectUrlFor(thumbName, thumbFile);
        const fullFile = fullName && imageFiles.get(fullName);
        if (fullFile) {
            const a = document.createElement("a");
            a.href = objectUrlFor(fullName, fullFile);
            a.target = "_blank";
            a.rel = "noopener";
            a.append(img);
            td.append(a);
        } else {
            td.append(img);
        }
    } else if (remoteHttpUrl(c.thumb) || remoteHttpUrl(c.url)) {
        // A web link (S3, an image host, ...). The thumbnail is small; the full image is the click-through.
        const thumbSrc = remoteHttpUrl(c.thumb) || remoteHttpUrl(c.url);
        const fullHref = remoteHttpUrl(c.url) || thumbSrc;
        const link = document.createElement("a");
        link.href = fullHref;
        link.target = "_blank";
        link.rel = "noopener noreferrer";
        if (loadRemoteInput.checked) {
            const img = document.createElement("img");
            img.className = "thumb";
            img.loading = "lazy";
            img.alt = "remote thumbnail";
            img.referrerPolicy = "no-referrer"; // don't tell the image host which page is asking
            img.addEventListener("error", () => {
                link.textContent = "failed to load (" + new URL(thumbSrc).hostname + ")";
                link.className = "muted";
            });
            img.src = thumbSrc;
            link.append(img);
        } else {
            link.className = "muted";
            link.textContent = "remote: " + new URL(thumbSrc).hostname;
        }
        td.title = fullHref;
        td.append(link);
    } else if (c.thumb || c.url) {
        // Image folder wasn't loaded, or the value isn't a web link we are willing to open.
        td.className = "muted nowrap";
        td.textContent = thumbName ? "missing: " + thumbName : "unsupported link";
        td.title = c.url || c.thumb;
    } else {
        td.className = "muted";
        td.textContent = "-";
    }
    return td;
}

/** Returns a normalized URL only for http(s) links; anything else (javascript:, data:, file:, ...) is refused. */
function remoteHttpUrl(value) {
    if (!value) return null;
    try {
        const u = new URL(value);
        return (u.protocol === "https:" || u.protocol === "http:") ? u.href : null;
    } catch {
        return null;
    }
}

function objectUrlFor(name, file) {
    if (!thumbUrls.has(name)) thumbUrls.set(name, URL.createObjectURL(file));
    return thumbUrls.get(name);
}

function flagsCell(c) {
    const td = document.createElement("td");
    const add = (text, bad) => {
        const b = document.createElement("span");
        b.className = "badge" + (bad ? " bad" : "");
        b.textContent = text;
        td.append(b);
    };
    if (c.deleted) add("deleted", true);
    if (c.uplinkSent) add("uplink sent");
    const r = regionOf(c.x, c.z);
    if (r.rx !== c.source.rx || r.rz !== c.source.rz) add("wrong file", true);
    if (!TYPE_NAMES[c.messageType - 1]) add("unknown type", true);
    return td;
}

function coordInput(c, axis, cls) {
    const input = document.createElement("input");
    input.type = "number";
    input.step = "1";
    input.className = cls;
    const key = "new" + axis.toUpperCase();
    input.value = c[key];
    input.addEventListener("input", () => {
        c[key] = input.value === "" ? NaN : Number(input.value);
        input.classList.toggle("invalid", !isValidCoord(axis, c[key]));
        updateTargetCell(c);
    });
    return input;
}

function isValidCoord(axis, value) {
    return Number.isInteger(value) && value >= LIMITS[axis][0] && value <= LIMITS[axis][1];
}

function targetFileName(c) {
    const { rx, rz } = regionOf(c.newX, c.newZ);
    return { rx, rz, name: `r.${rx}.${rz}.bin` };
}

function updateTargetCell(c) {
    const td = c.targetCell;
    if (!td) return;
    td.className = "nowrap";
    if (!(isValidCoord("x", c.newX) && isValidCoord("y", c.newY) && isValidCoord("z", c.newZ))) {
        td.classList.add("invalid-target");
        td.textContent = "invalid coordinates";
        return;
    }
    const t = targetFileName(c);
    const same = t.rx === c.source.rx && t.rz === c.source.rz;
    td.textContent = same ? t.name : `${t.name}  (moves from r.${c.source.rx}.${c.source.rz})`;
    if (!same) td.classList.add("moves");
}

// ---------- Position cell and /tp ----------
function tpCommand(dimDir, x, y, z) {
    const tp = `tp @s ${x} ${y} ${z}`;
    if (dimDir === "unknown") return "/" + tp;
    // "in" makes the command work from any dimension. Folder names use "+" where the id has ":".
    return `/execute in ${dimDir.replace("+", ":")} run ${tp}`;
}

async function copyText(text, button) {
    let ok = false;
    try {
        await navigator.clipboard.writeText(text);
        ok = true;
    } catch (e) {
        // Fallback for pages where the clipboard API is blocked (e.g. opened from a file).
        const ta = document.createElement("textarea");
        ta.value = text;
        document.body.append(ta);
        ta.select();
        try { ok = document.execCommand("copy"); } catch (e2) { ok = false; }
        ta.remove();
    }
    const old = button.textContent;
    button.textContent = ok ? "Copied!" : "Copy failed";
    setTimeout(() => { button.textContent = old; }, 1200);
}

function tpButton(label, title, getCommand) {
    const b = document.createElement("button");
    b.type = "button";
    b.className = "btn tiny secondary";
    b.textContent = label;
    b.title = title;
    b.addEventListener("click", () => {
        const cmd = getCommand();
        if (cmd) copyText(cmd, b);
    });
    return b;
}

function positionCell(c) {
    const td = document.createElement("td");
    td.className = "position";

    const now = document.createElement("div");
    now.className = "muted-line";
    now.textContent = `Old: ${c.x}, ${c.y}, ${c.z}`;

    const inputs = document.createElement("div");
    inputs.className = "xyz";
    for (const [axis, cls] of [["x", "x-input"], ["y", "y-input"], ["z", "z-input"]]) {
        const label = document.createElement("label");
        label.append(axis.toUpperCase() + " ", coordInput(c, axis, cls));
        inputs.append(label);
    }

    const buttons = document.createElement("div");
    buttons.className = "tp-buttons";
    buttons.append(
        tpButton("Copy /tp (Old)", "Copy a command that teleports you to the old position",
            () => tpCommand(c.source.dimDir, c.x, c.y, c.z)),
        tpButton("Copy /tp (New)", "Copy a command that teleports you to the new position",
            () => isValidCoord("x", c.newX) && isValidCoord("y", c.newY) && isValidCoord("z", c.newZ)
                ? tpCommand(c.source.dimDir, c.newX, c.newY, c.newZ) : null),
    );

    td.append(now, inputs, buttons);
    return td;
}

// Type chip, like count and warning badges stacked in one cell.
function typeCell(c) {
    const td = flagsCell(c);          // already a <td> holding the badges
    const top = document.createElement("div");
    top.style.whiteSpace = "nowrap";
    top.append(makeTypeChip(c.messageType));
    const likes = document.createElement("span");
    likes.className = "muted-line";
    likes.textContent = `  \u2665 ${c.like}`;
    top.append(likes);
    td.prepend(top);
    return td;
}

function buildRow(c) {
    const tr = document.createElement("tr");
    if (c.deleted) tr.className = "deleted";

    const msgTd = c.message ? cell(c.message, "msg") : cell("(no text)", "msg muted");
    const userTd = c.name ? cell(c.name) : cell("Anonymous", "muted");
    const timeTd = cell(c.timestamp ? new Date(c.timestamp).toLocaleString() : "-", "time");
    timeTd.title = `id ${c.id}`;

    c.targetCell = cell("", "nowrap");

    const selBox = document.createElement("input");
    selBox.type = "checkbox";
    selBox.checked = !!c.selected;
    selBox.addEventListener("change", () => {
        c.selected = selBox.checked;
        tr.classList.toggle("selected", c.selected);
        refreshSelectionUI();
    });
    c.checkbox = selBox;
    c.row = tr;
    if (c.selected) tr.classList.add("selected");

    tr.append(
        cell(selBox),
        cell(String(c.number)),
        thumbCell(c),
        userTd,
        msgTd,
        timeTd,
        typeCell(c),
        positionCell(c),
        c.targetCell,
    );
    updateTargetCell(c);
    return tr;
}

// ---------- Tools ----------
filterInput.addEventListener("input", renderTable);
loadRemoteInput.addEventListener("change", renderTable);
showDeletedInput.addEventListener("change", renderTable);
sortSelect.addEventListener("change", renderTable);
dateFrom.addEventListener("change", renderTable);
dateTo.addEventListener("change", renderTable);

function readShift() {
    return {
        dx: Number(document.getElementById("shiftX").value) || 0,
        dy: Number(document.getElementById("shiftY").value) || 0,
        dz: Number(document.getElementById("shiftZ").value) || 0,
    };
}

function shiftAll(list) {
    const { dx, dy, dz } = readShift();
    list.forEach(c => { c.newX += dx; c.newY += dy; c.newZ += dz; });
    renderTable();
}

document.getElementById("applyShiftBtn").addEventListener("click", () => {
    const scope = shiftScopeEl.value; // "" = every dimension
    // Only comments currently on screen are shifted, and only in the chosen dimension.
    shiftAll(shown.filter(c => !scope || c.source.dimDir === scope));
});

// Shifts exactly the ticked comments, whatever dimension they are in.
applySelectedBtn.addEventListener("click", () => shiftAll(comments.filter(c => c.selected)));

clearSelectionBtn.addEventListener("click", () => {
    comments.forEach(c => { c.selected = false; });
    renderTable();
});

document.getElementById("resetBtn").addEventListener("click", () => {
    comments.forEach(c => { c.newX = c.x; c.newY = c.y; c.newZ = c.z; });
    renderTable();
});

folderInput.addEventListener("change", e => handleFiles(e.target.files));
fileInput.addEventListener("change", e => handleFiles(e.target.files));

// ---------- Saving ----------
function download(blob, name) {
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = name;
    document.body.append(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 2000);
}

/** Build the output files: Map of "dimDir/r.X.Z.bin" -> Uint8Array. Throws on invalid input. */
function buildOutputs() {
    for (const c of comments) {
        for (const axis of ["x", "y", "z"]) {
            if (!isValidCoord(axis, c["new" + axis.toUpperCase()])) {
                throw new Error(`Comment #${c.number}: ${axis.toUpperCase()} must be a whole number between `
                    + `${LIMITS[axis][0]} and ${LIMITS[axis][1]}.`);
            }
        }
    }

    const groups = new Map(); // path -> array of record byte arrays, in load order
    let moved = 0;
    for (const c of comments) {
        const rec = c.raw.slice();
        const changed = c.newX !== c.x || c.newY !== c.y || c.newZ !== c.z;
        if (changed) {
            new DataView(rec.buffer).setBigUint64(32, packPos(c.newX, c.newY, c.newZ), false);
            moved++;
        }
        const t = targetFileName(c);
        const path = `${c.source.dimDir}/${t.name}`;
        if (!groups.has(path)) groups.set(path, []);
        groups.get(path).push(rec);
    }

    const outputs = new Map();
    for (const [path, records] of groups) {
        const total = records.reduce((n, r) => n + r.length, 0);
        const bytes = new Uint8Array(total);
        let off = 0;
        for (const r of records) { bytes.set(r, off); off += r.length; }
        outputs.set(path, bytes);
    }
    return { outputs, moved };
}

saveBtn.addEventListener("click", async () => {
    let built;
    try {
        built = buildOutputs();
    } catch (err) {
        statusEl.className = "status error";
        statusEl.textContent = err.message;
        return;
    }
    const { outputs, moved } = built;
    const notes = [`${moved} comment(s) changed position.`];

    if (outputs.size === 1) {
        const [path, bytes] = Array.from(outputs)[0];
        download(new Blob([bytes], { type: "application/octet-stream" }), path.split("/").pop());
        notes.push(`Downloaded ${path.split("/").pop()}.`);
    } else {
        const zip = new JSZip();
        for (const [path, bytes] of outputs) zip.file(`region/${path}`, bytes);
        const blob = await zip.generateAsync({ type: "blob" });
        download(blob, "world-comment-edited.zip");
        notes.push(`Downloaded world-comment-edited.zip with ${outputs.size} region file(s).`);
    }

    const emptied = Array.from(loadedPaths).filter(p => !outputs.has(p));
    if (emptied.length) {
        notes.push("These loaded files no longer contain any comments and were not written; "
            + "delete the old copies from your world: " + emptied.join(", "));
    }
    const unloaded = Array.from(outputs.keys()).filter(p => !loadedPaths.has(p));
    if (unloaded.length) {
        notes.push("These output files did not exist among the files you loaded. If your world already has a file "
            + "with the same name, comments in it that you did not load would be lost if you overwrite it: "
            + unloaded.join(", "));
    }
    statusEl.className = "status ok";
    statusEl.textContent = notes.join("\n");
});

// ---------- Light / dark theme ----------
const themeBtn = document.getElementById("themeBtn");
const systemDark = window.matchMedia("(prefers-color-scheme: dark)");

/** The theme actually in use: an explicit choice if there is one, otherwise the system setting. */
function currentTheme() {
    return document.documentElement.dataset.theme || (systemDark.matches ? "dark" : "light");
}

function updateThemeButton() {
    // The icons are in the HTML and chosen by CSS from the "is-dark" class; only the text for
    // the tooltip / screen readers (which names what a click will switch TO) is set here.
    const dark = currentTheme() === "dark";
    themeBtn.classList.toggle("is-dark", dark);
    const label = dark ? "Switch to light mode" : "Switch to dark mode";
    themeBtn.title = label;
    themeBtn.setAttribute("aria-label", label);
}

themeBtn.addEventListener("click", () => {
    const next = currentTheme() === "dark" ? "light" : "dark";
    document.documentElement.dataset.theme = next;
    try { localStorage.setItem("theme", next); } catch (e) { /* not saved, still applied */ }
    updateThemeButton();
});

// If the system theme changes while no explicit choice is saved, keep the button label correct.
systemDark.addEventListener("change", updateThemeButton);
updateThemeButton();
