function ricci_flow_sphere
% Discrete Ricci (Yamabe) flow on a triangulated sphere.
% Metric is conformally scaled: l_ij(u) = exp(u_i + u_j) * l_ij^0
% Curvature K_i is angle deficit: 2*pi - sum(face angles at i)
% Update: u_{t+dt} = u_t + dt * (K_target - K)

rng(0)

%% 1) Build a sphere mesh (icosphere)
subdiv = 3;                              % increase for finer mesh
[V,F]  = icosphere(subdiv);              % vertices V (nx3), faces F (mx3)
V      = normalize_rows(V);              % unit sphere
E      = unique_edges(F);
L0     = edge_lengths(V,E);              % base (reference) edge lengths

n  = size(V,1);
m  = size(F,1);

% Initial conformal factor u (perturb the metric)
u  = 0.2*randn(n,1);

% Target curvature: constant for sphere
K_target = (4*pi)/n * ones(n,1);         % total curvature 4π distributed evenly

% Time stepping params
dt       = 0.5;                          % stable for small steps
maxIter  = 400;
tol      = 1e-6;

% Colormap setup
cmap = turbo(256);

figure('Color','w'); 
for it = 1:maxIter
    % 2) Current scaled edge lengths
    L = scaled_edge_lengths(L0, u, E);
    
    % 3) Compute per-face angles from edge lengths
    theta = face_angles_from_edges(L, E, F); % (m x 3)
    
    % 4) Vertex curvatures (angle deficit)
    K = 2*pi*ones(n,1);
    for f = 1:m
        for loc = 1:3
            i = F(f,loc);
            K(i) = K(i) - theta(f,loc);
        end
    end
    
    % 5) Ricci flow update on conformal factor
    du = (K_target - K);
    u  = u + dt * du;
    
    % Convergence check (curvature infinity norm)
    err = norm(du, inf);
    
    % 6) Visualize: color by curvature error (K - mean K)
    Km = K - mean(K);
    cvals = rescale(Km, 0, 1);
    patch('Faces',F,'Vertices',V, ...
          'FaceVertexCData',interp1(linspace(0,1,256),cmap,cvals), ...
          'FaceColor','interp','EdgeColor',[0.7 0.7 0.7]);
    axis equal off
    camlight headlight; lighting gouraud
    title(sprintf('Discrete Ricci flow on S^2  |du|_∞ = %.2e  (iter %d)',err,it))
    drawnow
    
    if err < tol, break; end
end

% Final report
fprintf('Stopped at iter %d, |du|_inf = %.2e\n', it, err);

end

%% ---------- helpers ----------
function [V,F] = icosphere(subdiv)
% Minimal icosphere
[tV,tF] = icosahedron();
V = tV; F = tF;
for s = 1:subdiv
    [V,F] = loop_subdivide(V,F);
    V = normalize_rows(V);
end
end

function [V,F] = icosahedron()
t = (1+sqrt(5))/2;
V = [ -1,  t,  0;
      1,  t,  0;
     -1, -t,  0;
      1, -t,  0;
      0, -1,  t;
      0,  1,  t;
      0, -1, -t;
      0,  1, -t;
      t,  0, -1;
      t,  0,  1;
     -t,  0, -1;
     -t,  0,  1 ];
F = [ 1 12 6; 1 6 2; 1 2 8; 1 8 11; 1 11 12; ...
      2 6 10; 6 12 5; 12 11 3; 11 8 7; 8 2 9; ...
      4 10 5; 4 5 3; 4 3 7; 4 7 9; 4 9 10; ...
      5 10 6; 3 5 12; 7 3 11; 9 7 8; 10 9 2];
V = normalize_rows(V);
end

function [V2,F2] = loop_subdivide(V,F)
% Split each triangle into 4 by midpoints (no smoothing)
edgeMap = containers.Map('KeyType','char','ValueType','int32');
V2 = V; F2 = zeros(size(F,1)*4,3); faceIdx = 1;
for f = 1:size(F,1)
    i = F(f,1); j = F(f,2); k = F(f,3);
    a = mid_idx(i,j);
    b = mid_idx(j,k);
    c = mid_idx(k,i);
    F2(faceIdx,:) = [i a c]; faceIdx = faceIdx + 1;
    F2(faceIdx,:) = [a j b]; faceIdx = faceIdx + 1;
    F2(faceIdx,:) = [c b k]; faceIdx = faceIdx + 1;
    F2(faceIdx,:) = [a b c]; faceIdx = faceIdx + 1;
end

    function idx = mid_idx(p,q)
        if p>q, key = sprintf('%d_%d',q,p); else, key = sprintf('%d_%d',p,q); end
        if isKey(edgeMap,key)
            idx = edgeMap(key);
        else
            vm = (V(p,:)+V(q,:))/2;
            V2(end+1,:) = vm; %#ok<AGROW>
            idx = size(V2,1);
            edgeMap(key) = idx;
        end
    end
end

function Vn = normalize_rows(V)
Vn = V ./ vecnorm(V,2,2);
end

function E = unique_edges(F)
E = sort([F(:,[1,2]); F(:,[2,3]); F(:,[3,1])],2);
E = unique(E,'rows');
end

function L = edge_lengths(V,E)
d = V(E(:,1),:) - V(E(:,2),:);
L = sqrt(sum(d.^2,2));
end

function L = scaled_edge_lengths(L0,u,E)
L = L0 .* exp(u(E(:,1)) + u(E(:,2)));
end

function theta = face_angles_from_edges(L, E, F)
% Build per-face edge lengths from edge list, then use Law of Cosines
% For speed we map each face's three edges' lengths
edgeMap = containers.Map('KeyType','char','ValueType','double');
for e = 1:size(E,1)
    i = E(e,1); j = E(e,2);
    edgeMap(sprintf('%d_%d',i,j)) = L(e);
    edgeMap(sprintf('%d_%d',j,i)) = L(e);
end
m = size(F,1);
theta = zeros(m,3);
for f = 1:m
    i = F(f,1); j = F(f,2); k = F(f,3);
    lij = edgeMap(sprintf('%d_%d',i,j));
    ljk = edgeMap(sprintf('%d_%d',j,k));
    lki = edgeMap(sprintf('%d_%d',k,i));
    % angles opposite each edge
    theta(f,1) = law_of_cosine_angle(ljk, lki, lij); % at vertex i
    theta(f,2) = law_of_cosine_angle(lki, lij, ljk); % at vertex j
    theta(f,3) = law_of_cosine_angle(lij, ljk, lki); % at vertex k
end
end

function ang = law_of_cosine_angle(b,c,a)
% angle opposite side a in triangle with sides a,b,c
val = (b^2 + c^2 - a^2) / (2*b*c);
val = max(-1,min(1,val));     % clamp
ang = acos(val);
end

