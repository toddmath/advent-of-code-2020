use crate::prelude::*;
use std::mem;

pub struct Answer;

const WIDTH: usize = 10;
const SIDE: usize = 12;
const N_TILES: usize = SIDE * SIDE;
/// power of `2 >= N_TILES`
const N: usize = 256;
const MAX_EDGES: usize = 1 << WIDTH;
/// tile width in the bitmap
const W: usize = WIDTH - 2;
/// pixel width of final bitmap
const N_PIXELS: usize = SIDE * W;

pub type Edge = u16;
pub type Rotation = u8;
pub type TileNum = usize;
pub type EdgeMap = SmallVec<[SmallVec<[(TileNum, Rotation); 2]>; MAX_EDGES]>;
pub type Image = [[(TileNum, Rotation); SIDE]; SIDE];
pub type BitMap = BitVec<Lsb0, usize>;

#[inline]
fn flip_edge(edge: Edge) -> Edge {
    edge.reverse_bits() >> (8 * mem::size_of::<Edge>() - WIDTH)
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Tile {
    id: u16,
    /// edges `0 2 4 6` are normal, `1 3 5 7` are flipped
    edges: [u16; 8],
}

impl Tile {
    pub fn from_bytes(s: &mut &[u8]) -> Self {
        *s = s.advance(5);
        let id = parse_int_fast(s, 4, 4);
        *s = s.advance(1);

        let (mut up, mut right, mut down, mut left) = (0, 0, 0, 0);
        // up
        let top_row = *s;
        for i in 0..WIDTH {
            up |= ((top_row.get_at(i) == b'#') as u16) << i;
        }
        // down
        let bottom_row = (*s).advance((WIDTH - 1) * (WIDTH + 1));
        for i in 0..WIDTH {
            down |= ((bottom_row.get_at(i) == b'#') as u16) << (WIDTH - 1 - i);
        }
        // right
        let right_column = (*s).advance(WIDTH - 1);
        for i in 0..WIDTH {
            right |=
                ((right_column.get_at(i * (WIDTH + 1)) == b'#') as u16) << i;
        }
        // left
        let left_column = *s;
        for i in 0..WIDTH {
            left |= ((left_column.get_at(i * (WIDTH + 1)) == b'#') as u16)
                << (WIDTH - 1 - i);
        }

        *s = s.advance(WIDTH * (WIDTH + 1) + 1);

        // to turn: index = (index + 2 * angle) % 8 // (each turn is 90 deg; can
        // be negative) to flip: index = 7 - index
        let edges = [
            up,
            flip_edge(left),
            right,
            flip_edge(down),
            down,
            flip_edge(right),
            left,
            flip_edge(up),
        ];
        Self { id, edges }
    }
}

#[inline]
fn parse_tiles(mut s: &[u8]) -> SmallVec<[Tile; N]> {
    let mut tiles = SmallVec::new();
    for _ in 0..N_TILES {
        tiles.push(Tile::from_bytes(&mut s));
    }
    assert_eq!(s.len(), 0);
    tiles
}

#[inline]
fn get_bitmap_offsets(w: usize, h: usize) -> [(isize, isize, usize); 8] {
    const K: isize = N_PIXELS as _;
    [
        (1, K, 0),
        (K, 1, 0),
        (-K, 1, (w - 1) * N_PIXELS),
        (1, -K, (h - 1) * N_PIXELS),
        (-1, -K, (h - 1) * N_PIXELS + (w - 1)),
        (-K, -1, (w - 1) * N_PIXELS + (h - 1)),
        (K, -1, h - 1),
        (-1, K, w - 1),
    ]
}

#[inline]
fn parse_bitmap(mut s: &[u8], image: &Image) -> BitMap {
    let mut coords = [(0, 0, 0); N_TILES];
    for i in 0..SIDE {
        for j in 0..SIDE {
            coords[image[i][j].0] = (i, j, image[i][j].1);
        }
    }

    let offsets = get_bitmap_offsets(W, W);
    let mut bitmap = bitvec![0; N_PIXELS * N_PIXELS];

    for &(y, x, rot) in &coords {
        let (dx, dy, offset) = offsets[rot as usize];
        let mut offset = (offset + y * W * N_PIXELS + x * W) as isize;
        s = s.advance(WIDTH + 13);

        for _ in 0..W {
            let mut local_offset = offset;

            for i in 0..W {
                bitmap.set(local_offset as usize, s.get_at(i) == b'#');
                local_offset += dx;
            }

            s = s.advance(WIDTH + 1);
            offset += dy;
        }

        s = s.advance(WIDTH + 1);
    }

    bitmap
}

#[inline]
// fn build_edge_map(tiles: &[Tile]) -> EdgeMap {
fn build_edge_map(tiles: &SmallVec<[Tile; N]>) -> EdgeMap {
    // for each of the 1024 edges, track the list of tiles that have it along
    // with rotation
    let mut edge_map = EdgeMap::default();
    for _ in 0..MAX_EDGES {
        // let edge_map = edge_map.clone();
        edge_map.push(Default::default());
    }
    assert_eq!(tiles.len(), N_TILES);

    tiles.iter().enumerate().for_each(|(tile_num, tile)| {
        tile.edges.iter().enumerate().for_each(|(rotation, &edge)| {
            edge_map[edge as usize].push((tile_num, rotation as _));
            // edge_map[*edge as usize].push((tile_num, rotation as _));
        });
    });

    edge_map
}

#[inline]
fn find_boundary(edge_map: &EdgeMap) -> [usize; 4 * (SIDE - 1)] {
    // number of boundary edges for each tile
    let mut edge_counts = [0u8; N_TILES];

    for edge_parents in edge_map {
        if edge_parents.len() == 1 {
            let tile_num = edge_parents[0].0;
            edge_counts[tile_num] += 1;
        }
    }

    let mut boundary = [0; 4 * (SIDE - 1)];
    let (mut n_corners, mut n_edges) = (0, 0);

    for (tile_num, &n) in edge_counts.iter().enumerate() {
        if n == 2 {
            boundary[4 + n_edges] = tile_num;
            n_edges += 1;
        } else if n == 4 {
            boundary[n_corners] = tile_num;
            n_corners += 1;
        }
    }

    // first 4 tiles returned are corners, the rest are edges
    assert_eq!(n_corners, 4);
    assert_eq!(n_edges, 4 * (SIDE - 2));
    boundary
}

fn build_image(tiles: &[Tile], edge_map: &EdgeMap) -> Image {
    let mut image = [[(0, 0); SIDE]; SIDE];
    let tile_num = find_boundary(&edge_map)[0];

    let is_boundary = |i| {
        edge_map[tiles[tile_num].edges[(i as usize) % 8] as usize].len() == 1
    };
    let rotation = (0..8)
        .find(|&i| is_boundary(i) && is_boundary(i + 6))
        .unwrap();

    image[0][0] = (tile_num, rotation);

    for j in 1..SIDE {
        let (left_tile_num, left_rotation) = image[0][j - 1];
        let edge =
            tiles[left_tile_num].edges[7 - (left_rotation as usize + 2) % 8];
        let parents = &edge_map[edge as usize];
        let (tile_num, rotation) =
            parents[(parents[0].0 == left_tile_num) as usize];
        image[0][j] = (tile_num, (rotation + 2) % 8);
    }

    for i in 1..SIDE {
        for j in 0..SIDE {
            let (top_tile_num, top_rotation) = image[i - 1][j];
            let edge =
                tiles[top_tile_num].edges[7 - (top_rotation as usize + 4) % 8];
            let parents = &edge_map[edge as usize];
            image[i][j] = parents[(parents[0].0 == top_tile_num) as usize];
        }
    }

    if cfg!(debug_assertions) {
        check_image_for_correctness(tiles, edge_map, &image);
    }

    image
}

#[inline]
fn check_image_for_correctness(
    tiles: &[Tile],
    edge_map: &EdgeMap,
    image: &Image,
) {
    let mut tile_nums = (0..SIDE)
        .flat_map(|i| (0..SIDE).map(move |j| image[i][j].0))
        .collect_vec();
    tile_nums.sort_unstable();

    #[allow(clippy::needless_range_loop)]
    for i in 0..N_TILES {
        assert_eq!(tile_nums[i], i);
    }
    // (0..N_TILES).for_each(|i| assert_eq!(tile_nums[i], i));

    let n_parents = move |i: usize, j: usize, rot: usize| {
        edge_map[tiles[image[i][j].0].edges
            [((image[i][j].1 as usize) + rot) % 8] as usize]
            .len()
    };

    (0..SIDE).for_each(|i| {
        assert_eq!(n_parents(0, i, 0), 1); // top
        assert_eq!(n_parents(i, SIDE - 1, 2), 1); // right
        assert_eq!(n_parents(SIDE - 1, i, 4), 1); // bottom
        assert_eq!(n_parents(i, 0, 6), 1); // left
    });

    (1..SIDE - 1).for_each(|i| {
        (1..SIDE - 1).for_each(|j| {
            let (tile1, rot1) = (tiles[image[i][j].0], image[i][j].1);

            (0..4).for_each(|direction| {
                let (idx_a, idx_b) = match direction {
                    0 => (i - 1, j),
                    1 => (i, j + 1),
                    2 => (i + 1, j),
                    _ => (i, j - 1),
                };
                let (tile2, rot2) =
                    (tiles[image[idx_a][idx_b].0], image[idx_a][idx_b].1);
                let edge1 = tile1.edges[((rot1 + direction * 2) % 8) as usize];
                let edge2 =
                    tile2.edges[((rot2 + (direction + 2) * 2) % 8) as usize];
                assert_eq!(edge1, flip_edge(edge2));
            });
        });
    });
}

#[derive(Debug, Clone, Default)]
pub struct Mask {
    offsets: SmallVec<[usize; 64]>,
    width: usize,
    height: usize,
}

const ROT1: &[usize] = &[0, 4, 7, 3];

fn is_rot1(rot: &usize) -> bool {
    ROT1.contains(rot)
    // ROT1.iter().any(|x| *x == rot)
}

#[inline]
fn get_monster_masks() -> [Mask; 8] {
    let sea_monster_repr = [
        b"                  # ",
        b"#    ##    ##    ###",
        b" #  #  #  #  #  #   ",
    ];

    let width = sea_monster_repr[0].len();
    let height = sea_monster_repr.len();
    let offsets = get_bitmap_offsets(width, height);
    let mut masks: [Mask; 8] = Default::default();

    // const ROT1: &[usize] = &[0, 4, 7, 3];

    // let is_odd_rot = move |rot: usize| [0, 4, 7, 3].contains(&rot);

    for rotation in 0..8 {
        let mask = &mut masks[rotation];
        // masks.iter_mut().enumerate().for_each(|(rotation, mask)| {
        if is_rot1(&rotation) {
            mask.width = width;
            mask.height = height;
        } else {
            mask.width = height;
            mask.height = width;
        }

        let (dx, dy, offset) = offsets[rotation];
        let mut offset = offset as isize;

        // sea_monster_repr.iter().for_each(|&row| {
        //     let mut local_offset = offset;
        //     row.iter().for_each(|byte| {
        //         if byte == &b'#' {
        //             mask.offsets.push(local_offset as _);
        //         }
        //         local_offset += dx;
        //     });
        //     offset += dy;
        // });

        #[allow(clippy::needless_range_loop)]
        for y in 0..height {
            let mut local_offset = offset;
            for x in 0..width {
                if sea_monster_repr[y][x] == b'#' {
                    mask.offsets.push(local_offset as _);
                }
                local_offset += dx;
            }
            offset += dy;
        }
    }

    masks
}

#[derive(Debug, Clone, Copy)]
pub struct Cursor<T> {
    ptr: *const T,
}

impl<T> Cursor<T>
where
    T: Copy,
{
    #[inline(always)]
    pub fn step(&mut self) {
        self.jump(1);
    }

    #[inline(always)]
    pub fn jump(&mut self, n: usize) {
        unsafe { self.ptr = self.ptr.add(n) };
    }

    #[inline(always)]
    pub fn get(&mut self, n: usize) -> T {
        unsafe { *self.ptr.add(n) }
    }
}

impl Cursor<bool> {
    #[inline(always)]
    // pub fn check_mask(&mut self, offsets: &[usize]) -> bool {
    //     offsets.iter().all(|&offset| self.get(offset))

    //     // for &offset in offsets {
    //     //     if !self.get(offset) {
    //     //         return false;
    //     //     }
    //     // }
    //     // true
    // }

    pub fn check_masks(&mut self, offsets: &SmallVec<[usize; 64]>) -> bool {
        offsets.iter().all(|&offset| self.get(offset))
    }
}

#[inline]
fn count_monsters(bitmap: &BitMap, masks: &[Mask; 8]) -> u16 {
    let (mut x0, mut y0, mut rotation) = (0, 0, 0);
    let mut cursor: Cursor<bool> = Cursor {
        ptr: bitmap.as_raw_ptr() as *const _ as *const bool,
    };

    // iproduct!(0..N_PIXELS, 0..N_PIXELS, masks.iter().enumerate())

    'outer: for y in 0..N_PIXELS {
        for x in 0..N_PIXELS {
            for (i, mask) in masks.iter().enumerate() {
                let is_valid_mask = x < (N_PIXELS - mask.width)
                    && y < (N_PIXELS - mask.height)
                    && cursor.check_masks(&mask.offsets);

                if is_valid_mask {
                    x0 = x;
                    y0 = y;
                    rotation = i;
                    cursor.step();
                    break 'outer;
                }
            }

            cursor.step();
        }
    }

    let mut count = 1;
    let mask = &masks[rotation];

    for _ in x0 + 1..N_PIXELS - mask.width {
        if cursor.check_masks(&mask.offsets) {
            count += 1;
        }
        cursor.step();
    }

    cursor.jump(mask.width);

    for _ in y0 + 1..N_PIXELS - mask.height {
        for _ in 0..N_PIXELS - mask.width {
            if cursor.check_masks(&mask.offsets) {
                count += 1;
            }
            cursor.step();
        }

        cursor.jump(mask.width);
    }

    count
}

impl Solver for Answer {
    type Input = Vec<u8>;
    type Output1 = u64;
    type Output2 = u16;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        r.bytes().map(|res| res.unwrap()).collect_vec()
    }

    /// Correct: `45443966642567`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let tiles = parse_tiles(input);
        let edge_map = build_edge_map(&tiles);

        find_boundary(&edge_map)
            .par_iter()
            .take(4)
            .map(|&id| tiles[id].id as u64)
            .product()
    }

    /// Correct: `617`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let tiles = parse_tiles(input);
        let edge_map = build_edge_map(&tiles);
        let image = build_image(&tiles, &edge_map);
        let bitmap = parse_bitmap(input.as_slice(), &image);
        let masks = get_monster_masks();
        let n_monsters = count_monsters(&bitmap, &masks);

        bitmap.iter().map(|x| *x as u16).sum::<u16>()
            - (masks[0].offsets.len() as u16 * n_monsters)
    }
}
