'''Libraries'''
import pygame
from math import pi, atan2, sqrt, cos, sin, radians
from csv import reader, writer
from os import listdir
from random import randint
import numpy as np
pygame.init()

class Game():
    def __init__(self):
        '''Start Variables'''
        #Main Screen starting constants
        self.start_flag = True
        self.main_screen_size_x = 750
        self.main_screen_size_y = 750
        self.main_screen = pygame.display.set_mode((self.main_screen_size_x, self.main_screen_size_y), pygame.RESIZABLE)
        self.background_color = (0, 33, 130)
        self.accent_color = (236, 206, 247)
        self.blueprint_spacing = 25
        self.menu_width = 100
        self.tab_height = 85
        self.newX = self.menu_width + 1

        #Gametime starting constants
        self.game_font = pygame.freetype.SysFont("Arial", 30)
        self.saved = False
        self.exit_flag = False
        self.running = True
        self.dt = 0
        self.clock = pygame.time.Clock()
        self.times_averaged = 0
        self.average_fps = 0

        #Inputs starting constants
        pygame.mouse.set_cursor(pygame.cursors.arrow)
        self.hit = False
        self.mouse_lock = (False, None, None, None, 0, 0) #lock, object, mouse_x, mouse_y
        self.main_screen_x_center = self.main_screen_size_x / 2
        self.main_screen_y_center = self.main_screen_size_y / 2
        self.x_mouse = self.main_screen_x_center
        self.y_mouse = self.main_screen_y_center
        self.mouse_hitbox = (self.x_mouse, self.y_mouse, 0, 0)
        pygame.mouse.set_pos(self.x_mouse, self.y_mouse)
        self.mouse_layer = 1
        self.snap_mode = False
        self.selected_blockchain_id = 0
        self.obstacles = ()

        #Objects starting constants
        self.shape_id_blockchain = 0
        self.shape_lock = (False, None, None)
        self.shape_blockchain_ids = {}
        self.moving = False
        self.altering_point_1 = False
        self.altering_point_2 = False
        self.altering_point_3 = False
        self.expanding = False
        self.can_select = True
        self.select_countdown = 0

        #Fonts
        self.title_font = pygame.font.Font(None, 48)
        self.info_font = pygame.font.SysFont("Arial", 28)

        self.change_x_count = 0
        self.change_y_count = 0
        self.left_click = False

        self.selected_file = None
        self.current_file = None
        self.keys = []
        self.old_x = 0
        self.old_y = 0
        self.change_x = 0
        self.change_y = 0

        self.type = None
        self.camera_x = 0
        self.camera_y = 0
        self.zoom = 1.0
        self.camera_speed = 30
        self.pan_x = 0
        self.pan_y = 0
        self.panning = False

game = Game()

'''Shape Classes'''

class arc_object():
    def __init__(self, id, x1, y1, x2, y2, color, layer, surface):
        self.blockchain_id = id
        self.type = 'arc'
        self.layer = layer
        self.x = 0
        self.y = 0
        self.x1 = x1
        self.y1 = y1
        self.x2 = x2
        self.y2 = y2
        x3 = (x1 + x2) / 2 + 20
        y3 = (y1 + y2) / 2
        self.x3 = x3
        self.y3 = y3
        self.color = color
        self.surface = surface
        self.hitbox = (x1, y1, x2, y2)
        self.expansion_hitbox_1 = (x1 - 10, y1 - 10, 20, 20)
        self.expansion_hitbox_2 = (x2 - 10, y2 - 10, 20, 20)
        self.expansion_hitbox_3 = (x3 - 10, y3 - 10, 20, 20)
        self.can_lock = True
        self.locked = False
        self.start_angle = 0
        self.end_angle = 0
        self.selector_angle = 0

    def adjust_selector_point(self):
        offset = 1e-4  # Adjusting offset to prevent overlapping coordinates
        if self.x3 == self.x1:
            self.x3 += offset
        elif self.x3 == self.x2:
            self.x3 -= offset
        if self.y3 == self.y1:
            self.y3 += offset
        elif self.y3 == self.y2:
            self.y3 -= offset

    def circumcircle_calc(self):
        self.adjust_selector_point()
        y1, y2, y3 = -self.y1, -self.y2, -self.y3
        self.mid_x_1 = (self.x1 + self.x3) / 2
        self.mid_y_1 = (y1 + y3) / 2
        self.mid_x_2 = (self.x2 + self.x3) / 2
        self.mid_y_2 = (y2 + y3) / 2

        try:
            self.slope_1 = round((y3 - y1) / (self.x3 - self.x1), 6)
            if self.slope_1 != 0:
                self.slope_1_I = - (1 / self.slope_1)
                self.int_1_I = self.mid_y_1 - self.slope_1_I * self.mid_x_1
        except ZeroDivisionError:
            self.slope_1_I = 0

        try:
            self.slope_2 = round((y3 - y2) / (self.x3 - self.x2), 6)
            if self.slope_2 != 0:
                self.slope_2_I = - (1 / self.slope_2)
                self.int_2_I = self.mid_y_2 - self.slope_2_I * self.mid_x_2
        except ZeroDivisionError:
            self.slope_2_I = 0

        if self.slope_2 == 0:
            self.x_I = self.mid_x_2
        elif self.slope_1 == 0:
            self.x_I = self.mid_x_1
        else:
            self.x_I = (self.int_1_I - self.int_2_I) / (self.slope_1_I - self.slope_2_I)

        if self.slope_1 == 0:
            self.y_I = self.slope_2_I * self.x_I - self.int_2_I
        else:
            self.y_I = self.slope_1_I * self.x_I - self.int_1_I

        self.x_I = -self.x_I
        self.radius = sqrt(((self.x1 - self.x_I) ** 2) + ((y1 + self.y_I) ** 2))

        self.circumcircle_hitbox = (self.x_I - self.radius, (self.y_I - self.radius), self.radius * 2, self.radius * 2)

    def distance_to_line(self, x0, y0, x1, y1, x2, y2):
        numerator = abs((y2 - y1) * x0 - (x2 - x1) * y0 + x2 * y1 - y2 * x1)
        denominator = sqrt((y2 - y1) ** 2 + (x2 - x1) ** 2)
        return numerator / denominator if denominator != 0 else float('inf')


    def is_point_on_arc(self, center_x, cy, start_angle, end_angle, px, py):
        # Calculate the angle of the point (px, py) relative to the center (cx, cy)
        angle_point = atan2(py - cy, px - center_x)

        # Normalize the angles to be between [0, 2π]
        if start_angle < 0:
            start_angle += 2 * pi
        if end_angle < 0:
            end_angle += 2 * pi
        if angle_point < 0:
            angle_point += 2 * pi

        # Ensure the angles are in correct order (start_angle to end_angle) on the circle
        if start_angle > end_angle:
            start_angle, end_angle = end_angle, start_angle  # swap if needed for the arc's direction

        # Check if the angle of the point lies between start_angle and end_angle
        if start_angle <= angle_point <= end_angle:
            return True
        return False

    def draw(self):
        threshold = 10  # Distance threshold to switch from arc to line
        distance = self.distance_to_line(self.x3, self.y3, self.x1, self.y1, self.x2, self.y2)

        # Update hitboxes
        self.hitbox = (self.x1 + self.x, self.y1 + self.y, self.x2 + self.x, self.y2 + self.y)
        self.expansion_hitbox_1 = (self.x1 + self.x - 10 - game.camera_x, self.y1 + self.y - 10 - game.camera_y, 20, 20)
        self.expansion_hitbox_2 = (self.x2 + self.x - 10 - game.camera_x, self.y2 + self.y - 10 - game.camera_y, 20, 20)
        self.expansion_hitbox_3 = (self.x3 + self.x - 10 - game.camera_x, self.y3 + self.y - 10 - game.camera_y, 20, 20)

        if distance < threshold and self.can_lock:
            self.locked = True
            # If the selector is close to the line, draw a straight line
            self.mid_x_main = (self.x1 + self.x2) / 2
            self.mid_y_main = (self.y1 + self.y2) / 2
            self.x3 = self.mid_x_main
            self.y3 = self.mid_y_main
            pygame.draw.line(self.surface, self.color, 
                             (self.x1 + self.x - game.camera_x, self.y1 + self.y - game.camera_y), 
                             (self.x2 + self.x - game.camera_x, self.y2 + self.y - game.camera_y), 5)
        elif not self.can_lock or not (distance < threshold):
            self.locked = False
            try:
                # Calculate Circumcircle
                self.circumcircle_calc()            

                # Calculate angles for the points
                theta1 = atan2(self.y2 - self.y_I, self.x2 - self.x_I)
                theta2 = atan2(self.y1 - self.y_I, self.x1 - self.x_I)
                theta3 = atan2(self.y3 - self.y_I, self.x3 - self.x_I)

                # Invert the angles to match Pygame's y-axis
                self.start_angle = -theta1
                self.end_angle = -theta2
                self.selector_angle = -theta3

                # Normalize Angles
                if self.start_angle < 0:
                    self.start_angle += 2 * pi
                if self.end_angle < 0:
                    self.end_angle += 2 * pi
                if self.selector_angle < 0:
                    self.selector_angle += 2 * pi
                if self.start_angle > self.end_angle:
                    self.start_angle, self.end_angle = self.end_angle, self.start_angle

                # Swap if necessary
                if not (self.start_angle < self.selector_angle < self.end_angle):
                    self.start_angle, self.end_angle = self.end_angle, self.start_angle

                # Construct Arc
                pygame.draw.arc(self.surface, self.color, 
                                    (self.x_I - self.radius - game.camera_x, self.y_I - self.radius - game.camera_y, 
                                    self.radius * 2, self.radius * 2), 
                                    self.start_angle, self.end_angle, 1)
            except ZeroDivisionError:
                pass
            
        if game.type == "map_builder":
            # Draw hitboxes
            pygame.draw.rect(self.surface, "yellow", self.expansion_hitbox_1, 2)
            pygame.draw.rect(self.surface, "yellow", self.expansion_hitbox_2, 2)
            pygame.draw.ellipse(self.surface, "yellow", self.expansion_hitbox_3, 2)

class ellipse_object():
    def __init__(self, id, x, y, width, height, color, layer, surface):
        self.blockchain_id = id
        self.type = 'ellipse'
        self.layer = layer
        self.x = x
        self.y = y
        self.width = width
        self.height = height
        self.color = color
        self.surface = surface
        self.hitbox = (x - width / 2, y - height / 2, width, height)
        self.expansion_hitbox = (x + width / 2, y - (height / 2) - 20, 20, 20)
    
    def draw(self):
        self.hitbox = (self.x - self.width / 2 - game.camera_x, self.y - self.height / 2 - game.camera_y, self.width, self.height)
        self.expansion_hitbox = (self.x + self.width / 2 - game.camera_x, self.y - (self.height / 2) - 20 - game.camera_y, 20, 20)
        pygame.draw.ellipse(self.surface, self.color, self.hitbox)
        if game.type == "map_builder":
            pygame.draw.rect(self.surface, "yellow", self.expansion_hitbox, 2)

class rectangle_object():
    def __init__(self, id, x, y, width, height, color, layer, surface):
        self.blockchain_id = id
        self.type = 'rectangle'
        self.layer = layer
        self.x = x
        self.y = y
        self.width = width
        self.height = height
        self.color = color
        self.surface = surface
        self.hitbox = (x - width / 2, y - height / 2, width, height)
        self.expansion_hitbox = (x + width / 2, y - (height / 2) - 20, 20, 20)

    def draw(self):
        self.hitbox = (self.x - self.width / 2 - game.camera_x, self.y - self.height / 2 - game.camera_y, self.width, self.height)
        self.expansion_hitbox = (self.x + self.width / 2 - game.camera_x, self.y - (self.height / 2) - 20 - game.camera_y, 20, 20)
        pygame.draw.rect(self.surface, self.color, self.hitbox)
        if game.type == "map_builder":
            pygame.draw.rect(self.surface, "yellow", self.expansion_hitbox, 2)

'''Detection'''
def hitbox(hitbox_stationary, hitbox_mobile):
    if hitbox_mobile[0] >= hitbox_stationary[0] and hitbox_mobile[0] + hitbox_mobile[2] <= hitbox_stationary[0] + hitbox_stationary[2]:
        if hitbox_mobile[1] >= hitbox_stationary[1] and hitbox_mobile[1] + hitbox_mobile[3] <= hitbox_stationary[1] + hitbox_stationary[3]:
            return True
    return False

def hitline(hitbox_stationary, hitbox_mobile):
    try:
        slope = (hitbox_stationary[1]- hitbox_stationary[3]) / (hitbox_stationary[0] - hitbox_stationary[2])
        b = hitbox_stationary[1] - (slope * hitbox_stationary[0])
        greater = max(hitbox_stationary[0], hitbox_stationary[2])
        lesser = min(hitbox_stationary[0], hitbox_stationary[2])
        if (abs(hitbox_mobile[1] - (slope * hitbox_mobile[0] + b)) <= abs(8 * (1 + abs(slope)))) and (lesser <= hitbox_mobile[0] <= greater):
            return True
    except ZeroDivisionError:
        if abs(hitbox_mobile[0] - hitbox_stationary[0]) <= 8:
            return True
    return False

def hitarc(stationary_hitbox, mobile_hitbox):
    mx, my, mw, mh = mobile_hitbox
    center_x, center_y, radius, start_angle, stop_angle = stationary_hitbox

    corners = [
        (mx, my),  # Top-left corner
        (mx + mw, my),  # Top-right corner
        (mx, my + mh),  # Bottom-left corner
        (mx + mw, my + mh)  # Bottom-right corner
    ]

    for corner in corners:
        corner_x, corner_y = corner
        # Find the angle of the corner relative to the center of the arc
        angle = -atan2(corner_y - center_y, corner_x - center_x)
        if angle < 0:
            angle += 2 * pi  # Normalize angle
        
        # Check if the corner is within the angular bounds of the arc and within the radius
        distance_squared = (corner_x - center_x)**2 + (corner_y - center_y)**2
        if start_angle < angle < stop_angle and distance_squared <= radius**2:
            return True  # Collision detected (corner inside arc)

    # No collision detected
    return False

def hitellipse(hitbox_stationary, hitbox_mobile):
    x_test = hitbox_mobile[0]
    y_test = -hitbox_mobile[1]
    width = hitbox_stationary[2]
    height = hitbox_stationary[3]
    x_center = hitbox_stationary[0] + width / 2
    y_center = -(hitbox_stationary[1] + height / 2)
    x_axis = (width / 2) ** 2
    y_axis = (height / 2) ** 2
    
    test = (((x_test - x_center) ** 2) / x_axis) + (((y_test - y_center) ** 2) / y_axis)
    if test <= 1:
        return True
    return False

def hitborder(hitbox):
    """
    Checks to see if border has been overstepped by a shape or its expansion hitbox
    if it has, it moves the shape back to the border
    """
    x = 0
    y = 0
    hit = False
    left_x = hitbox[0]
    right_x = hitbox[0] + hitbox[2]
    top_y = hitbox[1]
    bottom_y = hitbox[1] + hitbox[3]
    if left_x < game.newX: x = game.newX - left_x
    elif right_x > game.main_screen_size_x: x = game.main_screen_size_x - right_x
    if top_y < 0: y = -top_y
    elif bottom_y > game.main_screen_size_y: y = game.main_screen_size_y - bottom_y
    
    if y != 0 or x != 0:
        hit = True
    changes = (x, y, hit)
    return(changes)
class menu_icon():
    def __init__(self, path, mount_coordinates, scale_factor, highlight_color, screen, job_function):
        self.path = path
        self.mount_coordinates = mount_coordinates
        self.scale_factor = scale_factor
        self.highlight_color = highlight_color
        self.screen = screen
        self.job_function = job_function

        self.icon = pygame.image.load(self.path).convert_alpha()
        self.icon_width = self.icon.get_size()[0]
        self.icon_height = self.icon.get_size()[1]
        self.final_size = (int(self.icon_width * self.scale_factor), int(self.icon_height * self.scale_factor))
        self.icon_final = pygame.transform.scale(self.icon, self.final_size)

        self.hitbox = (self.mount_coordinates[0], self.mount_coordinates[1], self.final_size[0], self.final_size[1])

    def draw(self):
        self.screen.blit(self.icon_final, (self.mount_coordinates[0], self.mount_coordinates[1]))

    def action(self):
        self.job_function()

def save_map():
    save_options_popup.execute = True

def exit_creator():
    if game.saved:
        game.running = False
    else:
        game.exit_flag = True

def copy_shape():    
    oobj = game.shape_blockchain_ids.get(game.selected_blockchain_id) #original object
    if oobj.type == "arc":
        copied_obstacle = arc_object(game.shape_id_blockchain, oobj.x1 - 50, oobj.y1 + 50, oobj.x2 - 50, oobj.y2 + 50, oobj.color, game.shape_id_blockchain + 1, oobj.surface)
        copied_obstacle.x3 - 50
        copied_obstacle.y3 + 50
    elif oobj.type == "rectangle":
        copied_obstacle = rectangle_object(game.shape_id_blockchain, oobj.x - 50, oobj.y + 50, oobj.width, oobj.height, oobj.color, game.shape_id_blockchain + 1, oobj.surface)
    elif oobj.type == "ellipse":
        copied_obstacle = ellipse_object(game.shape_id_blockchain, oobj.x - 50, oobj.y + 50, oobj.width, oobj.height, oobj.color, game.shape_id_blockchain + 1, oobj.surface)

    game.shape_blockchain_ids[copied_obstacle.blockchain_id] = copied_obstacle
    game.selected_blockchain_id = game.shape_id_blockchain
    game.mouse_layer = game.shape_id_blockchain + 1
    game.shape_id_blockchain += 1


def delete_shape():
    game.shape_blockchain_ids.pop(game.selected_blockchain_id, None)

def up_layer():
    obstacle = game.shape_blockchain_ids.get(game.selected_blockchain_id)
    higher_obstacle = None
    for obj in game.shape_blockchain_ids.values():
        if obj.layer == obstacle.layer + 1:
            higher_obstacle = game.shape_blockchain_ids.get(obj.blockchain_id)
            higher_obstacle.layer -= 1
            obstacle.layer += 1
            break
    if higher_obstacle == None:
        obstacle.layer += 1
    game.mouse_layer += 1
    
def down_layer():
    obstacle = game.shape_blockchain_ids.get(game.selected_blockchain_id)
    lower_obstacle = None
    if obstacle.layer == 1:
        return
    else:
        for obj in game.shape_blockchain_ids.values():
            if obj.layer == obstacle.layer -1:
                lower_obstacle = game.shape_blockchain_ids.get(obj.blockchain_id)
                lower_obstacle.layer += 1
                obstacle.layer -= 1
                break
        if lower_obstacle == None:
            obstacle.layer -= 1
        game.mouse_layer -= 1

def add_arc():
    new_arc = arc_object(game.shape_id_blockchain, game.main_screen_x_center, game.main_screen_y_center, game.main_screen_x_center + 50, game.main_screen_y_center + 50, "cyan", game.shape_id_blockchain + 1, game.main_screen)
    game.shape_blockchain_ids[new_arc.blockchain_id] = new_arc
    game.selected_blockchain_id = game.shape_id_blockchain
    game.mouse_layer = game.shape_id_blockchain + 1
    game.shape_id_blockchain += 1

def add_square():
    new_rectangle = rectangle_object(game.shape_id_blockchain, game.main_screen_x_center, game.main_screen_y_center, 75, 75, "green", game.shape_id_blockchain + 1, game.main_screen)
    game.shape_blockchain_ids[new_rectangle.blockchain_id] = new_rectangle
    game.selected_blockchain_id = game.shape_id_blockchain
    game.mouse_layer = game.shape_id_blockchain + 1
    game.shape_id_blockchain += 1

def add_ellipse():
    new_ellipse = ellipse_object(game.shape_id_blockchain, game.main_screen_x_center, game.main_screen_y_center, 100, 100, "purple", game.shape_id_blockchain + 1, game.main_screen)
    game.shape_blockchain_ids[new_ellipse.blockchain_id] = new_ellipse
    game.selected_blockchain_id = game.shape_id_blockchain
    game.mouse_layer = game.shape_id_blockchain + 1
    game.shape_id_blockchain += 1

save_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/save.png", (19.5, 12), 3.8125, "green", game.main_screen, save_map)
exit_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/exit.png", (19.5, 607), 3.8125, "green", game.main_screen, exit_creator)
copy_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/copy.png", (19.5, 437), 3.8125, "green", game.main_screen, copy_shape)
delete_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/delete.png", (19.5, 522), 3.8125, "green", game.main_screen, delete_shape)
up_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/up.png", (12, 352), 3.81255, "green", game.main_screen, up_layer)
down_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/down.png", (57, 352), 3.81255, "green", game.main_screen, down_layer)
arc_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/line.png", (19.5, 97), 3.81255, "green", game.main_screen, add_arc)
square_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/square.png", (19.5, 182), 3.81255, "green", game.main_screen, add_square)
ellipse_icon = menu_icon("Mechatronics II/Drone Course Simulator/Assets/ellipse.png", (19.5, 267), 3.81255, "green", game.main_screen, add_ellipse)

menu_icons = [save_icon, exit_icon, copy_icon, delete_icon, up_icon, down_icon, arc_icon, square_icon, ellipse_icon]

#Exit popup
exit_popup_width, exit_popup_height = 300, 200
exit_popup = pygame.Surface((exit_popup_width, exit_popup_height))
exit_popup.fill((200, 200, 200))
exit_popup_x, exit_popup_y = (game.main_screen_size_x - exit_popup_width) / 2, (game.main_screen_size_y - exit_popup_height) / 2

class Button():
    def __init__(self, screen, text, x_center, y_center, width, height, color, highlight_color, text_color):
        self.screen = screen
        self.text = text
        self.x_center = x_center
        self.y_center = y_center
        self.width = width
        self.height = height
        self.color = color
        self.highlight_color = highlight_color
        self.text_color = text_color

        self.locator_rect = pygame.Rect(x_center - width / 2, y_center - height / 2, width, height)
        self.projecting_screen = pygame.Surface((width, height))
        self.rendered_text = game.info_font.render(text, True, text_color)
        self.text_width = self.rendered_text.get_rect()[2]
        self.text_height = self.rendered_text.get_rect()[3]
        self.text_rect = ((width - self.text_width) / 2, (height - self.text_height) / 2, self.text_width, self.text_height)

    def draw(self):
        self.projecting_screen.fill(self.color)
        self.projecting_screen.blit(self.rendered_text, self.text_rect)
        self.screen.blit(self.projecting_screen, self.locator_rect)
        if hitbox(self.locator_rect, game.mouse_hitbox):
            pygame.draw.rect(game.main_screen, self.highlight_color, (self.locator_rect[0] - 2, self.locator_rect[1] - 2, self.locator_rect[2] + 4, self.locator_rect[3] + 4), 2)

    def is_clicked(self):
        if hitbox(self.locator_rect, game.mouse_hitbox):
            if game.can_select and game.left_click:
                game.can_select = False
                return True
        else:
            return False


def render_wrapped_text(text, font, color, text_width):
    words = text.split(' ')
    lines = []
    current_line = ""
    for word in words:
        test_line = f"{current_line} {word}".strip()
        # Check width if this word is added
        if font.size(test_line)[0] <= text_width:
            current_line = test_line
        else:
            lines.append(current_line)
            current_line = word

    # Add the last line
    if current_line:
        lines.append(current_line)

    line_surfaces = [font.render(line, True, color) for line in lines]
    line_height = font.get_linesize()
    text_height = line_height * len(line_surfaces)

    # Create a surface to hold all lines
    text_surface = pygame.Surface((text_width, text_height), pygame.SRCALPHA)

    # Blit each line onto the text_surface
    for i, line_surface in enumerate(line_surfaces):
        text_surface.blit(line_surface, (0, i * line_height))

    return text_surface


class popup():
    def __init__(self, screen, x_center, y_center, width, height, text, color, highlight_color, text_color):
        self.screen = screen
        self.x_center = x_center
        self.y_center = y_center
        self.width = width
        self.height = height
        self.text = text
        self.color = color
        self.highlight_color = highlight_color
        self.text_color = text_color

        self.locator_rect = pygame.Rect(x_center - width / 2, y_center - height / 2, width, height)
        self.projecting_screen = pygame.Surface((width, height))
        self.execute = True

        self.rendered_text = render_wrapped_text(text, game.info_font, text_color, width - 20)


    def draw(self):
        self.projecting_screen.fill(self.color)
        self.projecting_screen.blit(self.rendered_text, (10, 10))
        self.screen.blit(self.projecting_screen, self.locator_rect)

class ScrollMenu():
    def __init__(self, x, y, width, height, font, item_list, scroll_speed=20):
        self.x = x
        self.y = y
        self.width = width
        self.height = height
        self.font = font
        self.item_list = item_list
        self.scroll_speed = scroll_speed
        self.scroll_offset = 0
        #self.last_scroll_time = time.time()  # Track the last scroll time

    def handle_scroll_event(self, event):
        """Handle scroll events with delta time."""
        if event.type == pygame.MOUSEBUTTONDOWN:
            if event.button == 4:  # Scroll up
                self.scroll("up")
            elif event.button == 5:  # Scroll down
                self.scroll("down")

    def handle_selection_event(self, event):
        """Handle item selection on click."""
        if event.type == pygame.MOUSEBUTTONDOWN:
            mouse_x, mouse_y = event.pos
            if self.x <= mouse_x <= self.x + self.width and self.y <= mouse_y <= self.y + self.height:
                selected_index = (mouse_y - self.y) // 40 - 1  # Find which item was clicked
                if 0 <= selected_index < len(self.item_list):
                    selected_file = self.item_list[selected_index]
                    return selected_file  # Return selected item
        return None

    def draw(self, screen):
        """Draw the scrollable menu."""
        pygame.draw.rect(screen, "white", (self.x, self.y, self.width, self.height))
        
        # Draw the items in the list with scrolling
        for i, item in enumerate(self.item_list[self.scroll_offset:]):
            y_position = self.y + 20 + i * 40  # Adjust spacing between items
            if y_position > self.y + self.height:
                break
            item_text = self.font.render(item, True, "black")
            screen.blit(item_text, (self.x + 10, y_position))

    def scroll(self, direction):
        """Scroll the menu list with delta time."""
        #current_time = time.time()
        delta_time = game.dt  # Get time difference between scroll events
        
        if delta_time < 0.1:  # Prevent too rapid scrolling
            return  # Avoid updating scroll offset if the scroll is too quick
        
        if direction == "down" and self.scroll_offset + self.scroll_speed < len(self.item_list):
            self.scroll_offset += self.scroll_speed
        elif direction == "up" and self.scroll_offset - self.scroll_speed >= 0:
            self.scroll_offset -= self.scroll_speed
        
        #self.last_scroll_time = current_time  # Update the last scroll time

class TextBox():
    def __init__(self, x, y, width, height, font, color, bg_color, max_length=50):
        # Initialize the position, size, font, color, etc.
        self.rect = pygame.Rect(x, y, width, height)  # Rectangle for the text box
        self.font = font
        self.color = color
        self.bg_color = bg_color
        self.max_length = max_length  # Maximum number of characters allowed
        self.text = ""  # Text inside the box
        self.final_text = ""
        self.submit = False
        self.active = False  # Determines whether the text box is active for typing
        self.cursor_pos = len(self.text)  # Keeps track of where the cursor is in the text

    def handle_event(self, event):
        if event.type == pygame.MOUSEBUTTONDOWN:
            # Check if the mouse click is inside the box
            if self.rect.collidepoint(event.pos):
                self.active = True  # Set the text box as active
            else:
                self.active = False  # Deactivate if clicked outside
        
        if event.type == pygame.KEYDOWN:
            if self.active:
                if event.key == pygame.K_BACKSPACE:
                    # Handle backspace (delete last character)
                    self.text = self.text[:-1]
                elif event.key == pygame.K_RETURN:
                    # Handle enter (optional: can do something with the entered text)
                    self.submit = True
                elif len(self.text) < self.max_length and event.unicode.isprintable():
                    # Add character to text if it's printable and within max length
                    self.text += event.unicode

    def draw(self, screen):
        if self.submit:
            self.final_text = self.text
            self.active = False
        # Draw the text box with its background
        pygame.draw.rect(screen, self.bg_color, self.rect)
        pygame.draw.rect(screen, self.color, self.rect, 2)  # Border color
        
        # Render the text
        text_surface = self.font.render(self.text, True, self.color)
        screen.blit(text_surface, (self.rect.x + 5, self.rect.y + (self.rect.height - text_surface.get_height()) // 2))

        # Optionally, draw the cursor if the text box is active
        if self.active and pygame.time.get_ticks() % 1000 < 500:  # Blink every 500ms
            # Calculate the cursor's position after the last character
            cursor_x = self.rect.x + 5 + self.font.size(self.text)[0]  # The width of the text
            cursor_y = self.rect.y + (self.rect.height - self.font.get_height()) // 2
            pygame.draw.line(screen, self.color, (cursor_x, cursor_y), (cursor_x, cursor_y + self.font.get_height()), 2)

def exit_action_popup():
    showing = True
    while showing and game.running:
        critical_events()
        main_screen_background()
        draw_obstacles()
        main_screen_menu()
        get_user_inputs()
        exit_popup.fill((200, 200, 200))  # Clear previous renders
        game.game_font.render_to(exit_popup, (10, 10), "Test", (0, 0, 0))  # Black text at position (50, 80)
        game.main_screen.blit(exit_popup, (exit_popup_x, exit_popup_y))
        gametime_runner()

def critical_events():
    '''Critical Events'''
    game.selected_file = None
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            game.running = False
        if event.type == pygame.WINDOWRESIZED:
            game.main_screen_size_x, game.main_screen_size_y = pygame.display.get_window_size()[0], pygame.display.get_window_size()[1]
        text_box.handle_event(event)
        text_box_2.handle_event(event)
        

def main_screen_background():
    screen = game.main_screen
    zoom = game.zoom
    cam_x = game.camera_x
    cam_y = game.camera_y
    spacing = game.blueprint_spacing

    screen.fill(game.background_color)

    # Determine visible range in world coordinates
    screen_width, screen_height = game.main_screen_size_x, game.main_screen_size_y
    world_left = cam_x
    world_right = cam_x + screen_width / zoom
    world_top = cam_y
    world_bottom = cam_y + screen_height / zoom

    # Calculate grid line start positions aligned to the spacing
    start_x = int(world_left // spacing) * spacing
    end_x = int(world_right // spacing + 1) * spacing
    start_y = int(world_top // spacing) * spacing
    end_y = int(world_bottom // spacing + 1) * spacing

    # Vertical grid lines
    for x in range(start_x, end_x, spacing):
        screen_x = int((x - cam_x) * zoom)
        pygame.draw.line(screen, game.accent_color, (screen_x, 0), (screen_x, screen_height))

    # Horizontal grid lines
    for y in range(start_y, end_y, spacing):
        screen_y = int((y - cam_y) * zoom)
        pygame.draw.line(screen, game.accent_color, (0, screen_y), (screen_width, screen_y))


def main_screen_menu():
    '''Menu'''
    pygame.draw.rect(game.main_screen, "black", (0, 0, game.menu_width, game.main_screen_size_y))
    for i in range(9):
        pygame.draw.line(game.main_screen, "white", (0, i * game.tab_height), (game.menu_width, i * game.tab_height))
    pygame.draw.line(game.main_screen, "white", (game.menu_width, 0), (game.menu_width, game.main_screen_size_y))

    for icon in menu_icons:
        icon.draw()

def snap_mode_correct(x_coord, y_coord):
    if (x_coord - game.newX) % game.blueprint_spacing >= game.blueprint_spacing / 2:
        x_coord += game.blueprint_spacing - ((x_coord - game.newX) % game.blueprint_spacing)
    elif (x_coord - game.newX) % game.blueprint_spacing < game.blueprint_spacing / 2 and (x_coord - game.newX) % game.blueprint_spacing != 0:
        x_coord -= (x_coord - game.newX) % game.blueprint_spacing

    if (y_coord) % game.blueprint_spacing >= game.blueprint_spacing / 2:
        y_coord += game.blueprint_spacing - y_coord % game.blueprint_spacing
    elif y_coord % game.blueprint_spacing < game.blueprint_spacing / 2 and y_coord % game.blueprint_spacing != 0:
        y_coord -= y_coord % game.blueprint_spacing
    
    return (x_coord, y_coord)


def get_user_inputs():
    '''Keyboard Input'''
    dt = game.dt
    game.keys = pygame.key.get_pressed()
    if game.keys[pygame.K_x]:
        game.running = False
    if game.keys[pygame.K_LSHIFT] or game.keys[pygame.K_RSHIFT]:
        game.snap_mode = True
    else:
        game.snap_mode = False

    if game.keys[pygame.K_LEFT]:
        game.camera_x -= game.camera_speed * dt
    if game.keys[pygame.K_RIGHT]:
        game.camera_x += game.camera_speed * dt
    if game.keys[pygame.K_UP]:
        game.camera_y -= game.camera_speed * dt
    if game.keys[pygame.K_DOWN]:
        game.camera_y += game.camera_speed * dt

    '''Mouse Calculations'''
    game.old_x = game.x_mouse
    game.old_y = game.y_mouse
    game.x_mouse, game.y_mouse = pygame.mouse.get_pos()
    game.mouse_hitbox = (game.x_mouse, game.y_mouse, 0, 0)
    game.left_click = list(pygame.mouse.get_pressed())[0]

    game.change_x = game.x_mouse - game.old_x
    game.change_y = game.y_mouse - game.old_y
    if game.snap_mode:
        game.change_x_count += game.change_x
        game.change_y_count += game.change_y
        if abs(game.change_x_count) >= game.blueprint_spacing:
            game.change_x = game.change_x_count
            game.change_x_count = 0
        else:
            game.change_x = 0
        if abs(game.change_y_count) >= game.blueprint_spacing:
            game.change_y = game.change_y_count
            game.change_y_count = 0
        else:
            game.change_y = 0

    if (game.keys[pygame.K_LCTRL] or game.keys[pygame.K_RCTRL]) and game.left_click:
        game.panning = True
        game.camera_x -= game.change_x
        game.camera_y -= game.change_y
    else:
        game.panning = False


def draw_obstacles():
    '''Drawing Shapes'''
    game.obstacles = sorted(game.shape_blockchain_ids.values(), key = lambda x: x.layer)
    for shape in game.obstacles:
        shape.draw()

def gametime_runner():
    '''Gametime Runner'''
    if not game.can_select:
        game.select_countdown += game.dt
    if game.select_countdown >= 0.75:
        game.select_countdown = 0
        game.can_select = True

    pygame.display.flip()
    game.dt = game.clock.tick() / 1000
    game.times_averaged += 1
    if game.times_averaged == 0:
        game.average_fps = game.clock.get_fps()
    else:
        game.average_fps += (game.clock.get_fps() - game.average_fps) / game.times_averaged

start_read = "Welcome to the Tello drone simulator. Add shapes and obstacles and place them wherever you want. Hold SHIFT while moving to move in set increments."

spup = popup(game.main_screen, game.main_screen_x_center, game.main_screen_y_center, 400, 300, start_read, "black", "green", "white")
sbutton = Button(game.main_screen, "Get Started", game.main_screen_x_center, (spup.locator_rect[0] + spup.locator_rect[3]), 150, 100, "grey", "white", "black")

start_read_2 = "Would you like to coninue working on an old course, or start a new one?"
spup2 = popup(game.main_screen, game.main_screen_x_center, game.main_screen_y_center, 400, 200, start_read_2, "black", "green", "white")
sbutton2 = Button(game.main_screen, "New Course", game.main_screen_x_center - 125, (spup2.locator_rect[1] + spup2.locator_rect[3] - 35), 150, 70, "grey", "white", "black")
sbutton3 = Button(game.main_screen, "Edit Course", game.main_screen_x_center + 125, (spup2.locator_rect[1] + spup2.locator_rect[3] - 35), 150, 70, "grey", "white", "black")
spup2.execute = False

new_course_read = "Enter the name for your course"
new_course_popup = popup(game.main_screen, game.main_screen_x_center, game.main_screen_y_center, 400, 200, new_course_read, "black", "green", "white")
text_box = TextBox(new_course_popup.locator_rect[0], new_course_popup.locator_rect[1] + 80, 400, 40, game.info_font, "black", "white")
new_course_finish_button = Button(game.main_screen, "Finish", game.main_screen_x_center, (new_course_popup.locator_rect[1] + new_course_popup.locator_rect[3] - 35), 150, 70, "grey", "white", "black")
new_course_popup.execute = False

edit_course_read = "Enter the name for the course you would like to edit"
edit_course_popup = popup(game.main_screen, game.main_screen_x_center, game.main_screen_y_center, 400, 300, edit_course_read, "black", "green", "white")
all_files = listdir("Mechatronics II/Drone Course Simulator/Saved Maps")
text_box_2 = TextBox(new_course_popup.locator_rect[0], new_course_popup.locator_rect[1] + 80, 400, 40, game.info_font, "black", "white")
edit_course_finish_button = Button(game.main_screen, "Finish", game.main_screen_x_center, (new_course_popup.locator_rect[1] + new_course_popup.locator_rect[3] - 35), 150, 70, "grey", "white", "black")
edit_course_popup.execute = False

save_options_text = "Would you like to save this map under its old name, or save as a new one?"
save_options_popup = popup(game.main_screen, game.main_screen_x_center, game.main_screen_y_center, 400, 200, save_options_text, "black", "green", "white")
save_options_popup.execute = False
save_button = Button(game.main_screen, "Save", game.main_screen_x_center - 125, (save_options_popup.locator_rect[1] + save_options_popup.locator_rect[3] - 35), 150, 70, "grey", "white", "black")
save_as_button = Button(game.main_screen, "Save As", game.main_screen_x_center + 125, (save_options_popup.locator_rect[1] + save_options_popup.locator_rect[3] - 35), 150, 70, "grey", "white", "black")

saving_popup = popup(game.main_screen, game.main_screen_x_center, game.main_screen_y_center, 200, 100, "Saving", "black", "green", "white")
saving_popup.execute = False

def save_current_course():
    # Open the CSV file in write mode
    with open(game.current_file, mode='w', newline='') as file:
        writ = writer(file)
        
        # Write headers to the CSV file
        writ.writerow(['Key', 'ID', 'Type', 'Layer', 'X', 'Y'])

        # Loop through each item in the obstacle_dict
        for key, obj in game.shape_blockchain_ids.items():

            if isinstance(obj, arc_object):
                # Collect common attributes
                data = [
                    key,                # ID (key in dictionary)
                    obj.blockchain_id,
                    obj.type,
                    obj.layer,
                    obj.x,
                    obj.y,
                    obj.x1,
                    obj.y1,
                    obj.x2,
                    obj.y2,
                    obj.x3,
                    obj.y3,
                    obj.color,
                    obj.surface,
                    obj.hitbox,
                    obj.expansion_hitbox_1,
                    obj.expansion_hitbox_2,
                    obj.expansion_hitbox_3,
                    obj.can_lock,
                    obj.locked,
                    obj.start_angle,
                    obj.end_angle,
                    obj.selector_angle   
                    ]

            else:
                data = [
                    key,                # ID (key in dictionary)
                    obj.blockchain_id,           # Type (arc, ellipse, or rect)
                    obj.type,             # x1
                    obj.layer,             # y1
                    obj.x,             # x2
                    obj.y,             # y2
                    obj.width,          # color
                    obj.height,          # layer
                    obj.color,
                    obj.surface,
                    obj.hitbox,
                    obj.expansion_hitbox
                    ]

            # Write the row to the CSV file
            writ.writerow(data)


def process_file_load(file):
     with open(file, mode='r', newline='') as file:
        read = reader(file)
        next(read)  # Skip the header row
        
        """new_arc = arc_object(shape_id_blockchain, main_screen_x_center, main_screen_y_center, main_screen_x_center + 50, main_screen_y_center + 50, "cyan", shape_id_blockchain + 1, main_screen)
            shape_blockchain_ids[new_arc.blockchain_id] = new_arc"""

        for row in read:
            if row[2] == "arc":
                new_arc = arc_object(int(row[1]), float(row[6]), float(row[7]), float(row[8]), float(row[9]), row[12], int(row[3]), game.main_screen)
                new_arc.x3 = float(row[10])
                new_arc.y3 = float(row[11])
                game.shape_blockchain_ids[int(row[0])] = new_arc

                game.selected_blockchain_id = int(row[0])
                game.mouse_layer = game.shape_id_blockchain + 1
                game.shape_id_blockchain += 1


            elif row[2] == "rectangle":
                new_rectangle = rectangle_object(int(row[1]), float(row[4]), float(row[5]), float(row[6]), float(row[7]), row[8], int(row[3]), game.main_screen)
                game.shape_blockchain_ids[int(row[0])] = new_rectangle

                game.selected_blockchain_id = int(row[0])
                game.mouse_layer = game.shape_id_blockchain + 1
                game.shape_id_blockchain += 1

            elif row[2] == "ellipse":
                new_ellipse = ellipse_object(int(row[1]), float(row[4]), float(row[5]), float(row[6]), float(row[7]), row[8], int(row[3]), game.main_screen)
                game.shape_blockchain_ids[int(row[0])] = new_ellipse

                game.selected_blockchain_id = int(row[0])
                game.mouse_layer = game.shape_id_blockchain + 1
                game.shape_id_blockchain += 1

class Propellor():
    def __init__(self, path, center_coordinates, scale_factor, rotation_speed, screen):
        self.path = path
        self.center_coordinates = center_coordinates
        self.scale_factor = scale_factor
        self.screen = screen

        self.icon = pygame.image.load(self.path).convert_alpha()
        self.icon_width = self.icon.get_size()[0]
        self.icon_height = self.icon.get_size()[1]
        self.final_size = (int(self.icon_width * self.scale_factor), int(self.icon_height * self.scale_factor))
        self.icon_final = pygame.transform.scale(self.icon, self.final_size)

        self.angle = randint(0, 179)
        self.rotation_speed = rotation_speed

    def draw(self):
        """ Draw the propeller with center-based mounting and delta time-based rotation. """
        # Rotate the image
        rotated_image = pygame.transform.rotate(self.icon_final, self.angle)

        # Get the rotated image's rect and center it at the given coordinates
        rect = rotated_image.get_rect(center=self.center_coordinates)
        self.screen.blit(rotated_image, rect)

        # Update the angle
        self.angle = (self.angle + self.rotation_speed * game.dt) % 360

def simulator_exit():
    """FPS Check and Game Exit"""
    print("Sim Exit")
    print(f'Average FPS: {round(game.average_fps)}')
    pygame.quit()

class Drone():
    def __init__(self, obstacle_map, center_coordinates, orientation = 0):
        self.sprite_path = "Mechatronics II/Drone Course Simulator/Assets/Drone_Disconnected_No_Prop.png"
        self.center_coordinates = (center_coordinates[0] + game.newX, center_coordinates[1])  # Now the center of the drone
        self.scale_factor = 2.5
        self.screen = game.main_screen
        self.obstacle_map = obstacle_map
        self.speed_multipler = 1
        self.animating_command = False
        
        # Add the rotation angle
        self.rotation_angle = orientation  # Initialize the drone facing 0 degrees (up)
        self.height = 0

        # New: Queue for storing commands
        self.command_queue = []
        self.active_command = None
        self.active_args = None
        self.executing_commands = True
        self.wait_time = 0
        self.waiting = True
        self.buffer_time = 0.75

        # Load and scale image
        self.icon = pygame.image.load(self.sprite_path).convert_alpha()
        self.icon_width, self.icon_height = self.icon.get_size()
        self.final_size = (int(self.icon_width * self.scale_factor), int(self.icon_height * self.scale_factor))
        self.icon_final = pygame.transform.scale(self.icon, self.final_size)

    def _rotate_ccw(self, angle):
        speed = 72 #deg/s
        dt = game.dt

        est_time = angle / speed
        percent = dt / est_time
        ang = percent * angle
        if percent >= 0.95:
            move_angle = self.active_args
            self.animating_command = False
        else:
            move_angle = ang
        self.active_args -= ang
        """
        Rotate the drone clockwise by the specified angle over a given duration (in milliseconds).
        :param angle: The total angle to rotate by.
        :param duration: The time duration for the full rotation in milliseconds.
        """
        initial_angle = self.rotation_angle
        # Gradually interpolate between the initial and target angle
        self.rotation_angle = (initial_angle - move_angle) % 360
        self.waiting = True

    def _rotate_cw(self, angle):
        speed = 72 #deg/s
        dt = game.dt

        est_time = angle / speed
        percent = dt / est_time
        ang = percent * angle
        if percent >= 0.95:
            move_angle = self.active_args
            self.animating_command = False
            self.waiting = True
        else:
            move_angle = ang
        self.active_args -= ang
        """
        Rotate the drone clockwise by the specified angle over a given duration (in milliseconds).
        :param angle: The total angle to rotate by.
        :param duration: The time duration for the full rotation in milliseconds.
        """
        initial_angle = self.rotation_angle
        # Gradually interpolate between the initial and target angle
        self.rotation_angle = (initial_angle + move_angle) % 360

    @staticmethod
    def calculate_circumcircle(x1, y1, z1, x2, y2, z2):
        y1 = -y1
        y2 = -y2
        #Direction vectors from Drone center at (0,0,0)
        D_ab = (x1, y1, z1)
        D_ac = (x2, y2, z2)

        #Midpoints of those vectors
        M_ab = (x1 / 2, y1 / 2, z1 / 2)
        M_ac = (x2 / 2, y2 / 2, z2 / 2)

        #Othographic Normal to those vectors (Normal vector to plane of those 3 points and 2 vectors)
        N = np.linalg.cross(D_ab, D_ac)

        #Direction vectors for the planar orthagonal bisectors of the original direcion vectors
        D_bab = np.linalg.cross(N, D_ab)
        D_bac = np.linalg.cross(N, D_ac)

        #Solve various cases for parametric intercept "t"
        N1 = D_bac[0] * (M_ab[1] - M_ac[1]) - D_bac[1] * (M_ab[0] - M_ac[0])
        N2 = D_bac[0] * (M_ab[2] - M_ac[2]) - D_bac[2] * (M_ab[0] - M_ac[0])
        N3 = D_bac[2] * (M_ab[1] - M_ac[1]) - D_bac[1] * (M_ab[2] - M_ac[2])

        D1 = D_bab[0] * D_bac[1] - D_bac[0] * D_bab[1]
        D2 = D_bab[0] * D_bac[2] - D_bac[0] * D_bab[2]
        D3 = D_bab[2] * D_bac[1] - D_bac[2] * D_bab[2]

        #Avoid 0 division when bisector vectors are only skewed in a plane and not intercepting
        if D1 != 0:
            T_bi = N1 / D1
        elif D2 != 0:
            T_bi = N2 / D2
        else:
            T_bi = N3 / D3

        #Bisectors intercept
        P_bi = (M_ab[0] + T_bi * D_bab[0], M_ab[1] + T_bi * D_bab[1], M_ab[2] + T_bi * D_bab[2])
        P_bi = (P_bi[0], -P_bi[1], P_bi[2])  # Flip Y

        #Circumcircle radius
        R_cc = sqrt((P_bi[0] ** 2) + (P_bi[1] ** 2) + (P_bi[2] ** 2))

        #Scalar reference unit vector 1 (Orthagonal to N and SV2 on plane ABC, made with cross of N and (1,0,1))
        P_d1 = (N[1], -(N[0] - N[2]), -N[1])
        P_d1m = sqrt((P_d1[0] ** 2) + (P_d1[1] ** 2) + (P_d1[2] ** 2))
        S_v1 = (P_d1[0] / P_d1m, -P_d1[1] / P_d1m, P_d1[2] / P_d1m)



        #Scalar reference unit vector 2 (Orthagonal to N and SV1 on plane ABC, made with cross of N and (0,1,0))
        P_d2 = (-N[2], 0, N[0])
        P_d2m = sqrt((P_d2[0] ** 2) + (P_d2[1] ** 2) + (P_d2[2] ** 2))
        S_v2 = (P_d2[0] / P_d2m, -P_d2[1] / P_d2m, P_d2[2] / P_d2m)

        #Parametric circumcircle graphed by C_{x,y,z >> i}(t)-> (P_bi)[i] + R_cc * ((S_v1)[i] * cos(t) + (S_v2)[i] * sin(t))
        

        """Compute t range such that the circumcircular arc starts at the drone (0,0,0),
        and ends with the farthest point B or C such that all three points are passed through"""

        @staticmethod
        def get_t(point):
            rel = (np.array(point) - np.array((P_bi[0], P_bi[1], P_bi[2]))) / R_cc
            a = np.dot(rel, np.array((S_v1[0], S_v1[1], S_v1[2])))
            b = np.dot(rel, np.array((S_v2[0], S_v2[1], S_v2[2])))
            return np.arctan2(b, a) % (2 * np.pi)

        t0 = get_t([0, 0, 0])
        t1 = get_t((x1, y1, z1))
        t2 = get_t((x2, y2, z2))

        # Choose the larger t value to ensure passing through both points
        t_candidates = np.array([t1, t2])
        deltas = (t_candidates - t0) % (2 * np.pi)
        t_end = t0 + np.max(deltas)

        print("Arc start local:", P_bi[0] + R_cc * (S_v1[0] * cos(0) + S_v2[0] * sin(0)), P_bi[1] + R_cc * (S_v1[1] * cos(0) + S_v2[1] * sin(0)))

        return t0, t_end, t0, t1, t2, P_bi, R_cc, S_v1, S_v2

    def _curve(self, x1, y1, z1, x2, y2, z2):
        speed = 150  # cm/s
        dt = game.dt
        current_t = self.active_args[0]

        if not hasattr(self, 'arc_anchor'):
            self.arc_anchor = self.center_coordinates
        anchor_x, anchor_y = self.arc_anchor

        if len(self.active_args) < 3:
            result = self.calculate_circumcircle(x1, y1, z1, x2, y2, z2)
            self.active_args = list(self.active_args)
            self.active_args.append((result[5], result[6], result[7], result[8], result[1], result[0]))
            current_t = result[0]
            self.active_args[0] = current_t

        center, radius, sv1, sv2, t_end, t0_value = self.active_args[2]

        # ✅ Compute how much to increment t based on arc speed
        arc_dist = speed * dt
        delta_t = arc_dist / radius
        next_t = current_t + delta_t

        if next_t > t_end:
            next_t = t_end

        lx = center[0] + radius * (sv1[0] * cos(next_t) + sv2[0] * sin(next_t))
        ly = center[1] + radius * (sv1[1] * cos(next_t) + sv2[1] * sin(next_t))
        wx = anchor_x + lx
        wy = anchor_y + ly

        self.center_coordinates = (wx, wy)
        self.active_args[0] = next_t

        if next_t >= t_end:
            del self.arc_anchor
            self.animating_command = False
            self.waiting = True

    def _backward(self, distance):
        """
        Move the drone forward by the specified distance in the direction it is facing.
        :param distance: The distance to move.
        """
        speed = 150 #cm/s
        dt = game.dt

        est_time = distance / speed
        percent = dt / est_time
        dist = percent * distance
        if percent >= 0.95:
            move_dist = -self.active_args
            self.animating_command = False
        else:
            move_dist = -dist
        self.active_args -= dist
        # Convert the rotation angle to radians
        angle_radians = radians(self.rotation_angle)  # Invert the angle to match Pygame's coordinates

        # Calculate the movement vector
        dx = move_dist * cos(angle_radians)
        dy = move_dist * sin(angle_radians)

        # Update the drone's position
        new_x = self.center_coordinates[0] + dx
        new_y = self.center_coordinates[1] + dy  # Add dy since Pygame's y-axis increases downward

        # Set the new coordinates
        self.center_coordinates = (new_x, new_y)
        self.waiting = True

    def _forward(self, distance):
        """
        Move the drone forward by the specified distance in the direction it is facing.
        :param distance: The distance to move.
        """
        speed = 150 #cm/s
        dt = game.dt

        est_time = distance / speed
        percent = dt / est_time
        dist = percent * distance
        if percent >= 0.95:
            move_dist = self.active_args
            self.animating_command = False
        else:
            move_dist = dist
        self.active_args -= dist
        # Convert the rotation angle to radians
        angle_radians = radians(self.rotation_angle)  # Invert the angle to match Pygame's coordinates

        # Calculate the movement vector
        dx = move_dist * cos(angle_radians)
        dy = move_dist * sin(angle_radians)

        # Update the drone's position
        new_x = self.center_coordinates[0] + dx
        new_y = self.center_coordinates[1] + dy  # Add dy since Pygame's y-axis increases downward

        # Set the new coordinates
        self.center_coordinates = (new_x, new_y)
        self.waiting = True

    def _right(self, distance):
        """
        Move the drone Right by the specified distance.
        :param distance: The distance to move.
        """
        speed = 150 #cm/s
        dt = game.dt

        est_time = distance / speed
        percent = dt / est_time
        dist = percent * distance
        if percent >= 0.95:
            move_dist = self.active_args
            self.animating_command = False
        else:
            move_dist = dist
        self.active_args -= dist
        # Convert the rotation angle to radians
        angle_radians = radians(self.rotation_angle + 90)  # Invert the angle to match Pygame's coordinates

        # Calculate the movement vector
        dx = move_dist * cos(angle_radians)
        dy = move_dist * sin(angle_radians)

        # Update the drone's position
        new_x = self.center_coordinates[0] + dx
        new_y = self.center_coordinates[1] + dy  # Add dy since Pygame's y-axis increases downward

        # Set the new coordinates
        self.center_coordinates = (new_x, new_y)
        self.waiting = True

    def _left(self, distance):
        """
        Move the drone Left by the specified distance.
        :param distance: The distance to move.
        """
        speed = 150 #cm/s
        dt = game.dt

        est_time = distance / speed
        percent = dt / est_time
        dist = percent * distance
        if percent >= 0.95:
            move_dist = self.active_args
            self.animating_command = False
        else:
            move_dist = dist
        self.active_args -= dist
        # Convert the rotation angle to radians
        angle_radians = radians(self.rotation_angle - 90)  # Invert the angle to match Pygame's coordinates

        # Calculate the movement vector
        dx = move_dist * cos(angle_radians)
        dy = move_dist * sin(angle_radians)

        # Update the drone's position
        new_x = self.center_coordinates[0] + dx
        new_y = self.center_coordinates[1] + dy  # Add dy since Pygame's y-axis increases downward

        # Set the new coordinates
        self.center_coordinates = (new_x, new_y)
        self.waiting = True
    
    def _land(self):
        print("Landed")

    def _up(self, distance):
        speed = 15 #cm/s
        dt = game.dt

        est_time = distance / speed
        percent = dt / est_time
        dist = percent * distance
        
        if percent >= 0.95:
            print("EE")
            move_dist = self.active_args
            self.animating_command = False
        else:
            move_dist = dist
        self.active_args -= dist
        """
        Rotate the drone clockwise by the specified angle over a given duration (in milliseconds).
        :param angle: The total angle to rotate by.
        :param duration: The time duration for the full rotation in milliseconds.
        """
        self.height += move_dist
        self.waiting = True
        print(self.height)

    def _down(self, distance):
        speed = 15 #cm/s
        dt = game.dt

        est_time = distance / speed
        percent = dt / est_time
        dist = percent * distance
        if percent >= 0.95:
            print("EE")
            move_dist = self.active_args
            self.animating_command = False
        else:
            move_dist = dist
        self.active_args -= dist
        """
        Rotate the drone clockwise by the specified angle over a given duration (in milliseconds).
        :param angle: The total angle to rotate by.
        :param duration: The time duration for the full rotation in milliseconds.
        """
        self.height -= move_dist
        self.waiting = True

    def _wait(self, time):
        self.wait_time += game.dt
        if self.wait_time >= time + self.buffer_time:
            self.animating_command = False
            self.wait_time = 0

    """Queueing Operations"""
    def forward(self, distance):
        """Queue a forward movement command."""
        self.command_queue.append(("forward", distance))

    def rotate_cw(self, angle):
        """Queue a clockwise rotation command."""
        self.command_queue.append(("rotate_cw", angle))

    def rotate_ccw(self, angle):
        """Queue a counterclockwise rotation command."""
        self.command_queue.append(("rotate_ccw", angle))

    def wait(self, time):
        self.command_queue.append(("wait", time))

    def land(self):
        """Queue a land command."""
        self.command_queue.append(("land",))

    def up(self, distance):
        self.command_queue.append(("up", distance))
    
    def down(self, distance):
        self.command_queue.append(("down", distance))

    def curve(self, x1, y1, z1, x2, y2, z2):
        t = 0
        self.command_queue.append(("curve", (t, (x1, y1, z1, x2, y2, z2))))

    def backward(self, distance):
        self.command_queue.append(("backward", distance))

    def right(self, distance):
        self.command_queue.append(("right", distance))

    def left(self, distance):
        self.command_queue.append(("left", distance))

    # New: Execute the next command in the queue
    def execute_next_command(self):
        """Execute the next queued command, if any."""            
        if self.animating_command:
            if self.active_command == "forward":
                self._forward(self.active_args)
            elif self.active_command == "rotate_cw":
                self._rotate_cw(self.active_args)
            elif self.active_command == "rotate_ccw":
                self._rotate_ccw(self.active_args)
            elif self.active_command == "land":
                pass
            elif self.active_command == "wait":
                self._wait(self.active_args)
            elif self.active_command == "up":
                self._up(self.active_args)
            elif self.active_command == "down":
                self._down(self.active_args)
            elif self.active_command == "curve":
               self._curve(*self.active_args[1])
            elif self.active_command == "backward":
                self._backward(self.active_args)
            elif self.active_command == "right":
                self._right(self.active_args)
            elif self.active_command == "left":
                self._left(self.active_args)
        
        else:
            if self.waiting:
                self.active_command, self.active_args = "wait", self.buffer_time
                self.animating_command = True
                self.waiting = False
            else:
                try:
                    self.active_command, self.active_args = self.command_queue.pop(0)
                    self.animating_command = True
                except IndexError:
                    self.executing_commands = False
    
    # Start Sim
    def launch(self):
        drone_flyer(self, self.obstacle_map)

    def draw(self):
        if self.executing_commands:
            self.execute_next_command()
        """ Draw the drone centered on its coordinates """
        # Rotate the image based on the current angle
        coordinate = (self.center_coordinates[0] - game.camera_x, self.center_coordinates[1] - game.camera_y)
        rotated_image = pygame.transform.rotate(self.icon_final, -self.rotation_angle)  
        rect = rotated_image.get_rect(center = coordinate)
        self.screen.blit(rotated_image, rect)

speed = 160000
prop1 = Propellor("Mechatronics II/Drone Course Simulator/Assets/Prop.png", (25 + game.newX, 100), 2.5, speed, game.main_screen)
prop2 = Propellor("Mechatronics II/Drone Course Simulator/Assets/Prop.png", (92.5 + game.newX, 100), 2.5, speed, game.main_screen)
prop3 = Propellor("Mechatronics II/Drone Course Simulator/Assets/Prop.png", (25 + game.newX, 175), 2.5, speed, game.main_screen)
prop4 = Propellor("Mechatronics II/Drone Course Simulator/Assets/Prop.png", (92.5 + game.newX, 175), 2.5, speed, game.main_screen)
drone_propellors = [prop1, prop2, prop3, prop4]


#from Drone_Course_Simulator import Drone
#tello = Drone(None, (60, 135), None)
#tello.forward(100)

def map_maker():
    game.type = "map_builder"
    counter = 0
    stopper = False

    """MAIN GAMELOOP"""
    while game.running:  
        critical_events()
        main_screen_background()
        draw_obstacles()
        main_screen_menu()
        get_user_inputs()
        
        if spup.execute:
            spup.draw()
            sbutton.draw()
            if sbutton.is_clicked():
                spup.execute = False
                spup2.execute = True
        
        elif spup2.execute:
            spup2.draw()
            sbutton2.draw()
            sbutton3.draw()
            if sbutton2.is_clicked():
                spup2.execute = False
                new_course_popup.execute = True

            elif sbutton3.is_clicked():
                spup2.execute = False
                edit_course_popup.execute = True
        
        elif new_course_popup.execute:
            new_course_popup.draw()
            new_course_finish_button.draw()
            text_box.draw(game.main_screen)

            if new_course_finish_button.is_clicked():
                text_box.submit = True

            elif text_box.submit:
                new_course_name = text_box.final_text
                new_course_popup.execute = False

                # Define the path manually
                filepath = f"Mechatronics II/Drone Course Simulator/Saved Maps/{new_course_name}.csv"

                # Create an empty CSV file
                with open(filepath, "w") as file:
                    pass  # Just creates the file without writing anything`

                game.current_file = filepath
        
        elif edit_course_popup.execute:
            edit_course_popup.draw()
            edit_course_finish_button.draw()
            text_box_2.draw(game.main_screen)

            if edit_course_finish_button.is_clicked():
                text_box_2.submit = True

            elif text_box_2.submit:
                edit_course_name = f"{text_box_2.final_text}.csv"
                if edit_course_name not in all_files:
                    text_box_2.submit = False
                    text_box_2.text = ""
                else:
                    game.current_file = f"Mechatronics II/Drone Course Simulator/Saved Maps/{edit_course_name}"

                    process_file_load(game.current_file)

                    edit_course_popup.execute = False


        elif save_options_popup.execute:
            save_options_popup.draw()
            save_button.draw()
            save_as_button.draw()
            
            if save_button.is_clicked():
                save_current_course()
                
        else:  
            for icon in menu_icons:
                if hitbox(icon.hitbox, game.mouse_hitbox):
                    highlight_box = (icon.hitbox[0] - 2, icon.hitbox[1] - 2, icon.hitbox[2] + 4, icon.hitbox[3] + 4)
                    pygame.draw.rect(game.main_screen, "white", highlight_box, 2)
                    if not(game.moving or game.expanding):
                        if game.can_select and game.left_click:
                            icon.action()
                            game.can_select = False

            '''Calculating Shapes Physics'''
            obstacles = sorted(game.shape_blockchain_ids.values(), key = lambda x: x.layer, reverse = True)
            for shape in obstacles:
                """Calculate New Mouse layer"""
                if not (game.moving or game.altering_point_1 or game.altering_point_2 or game.altering_point_3 or game.expanding):
                    if shape.type == 'arc' and (hitbox(shape.expansion_hitbox_1, game.mouse_hitbox) or hitbox(shape.expansion_hitbox_2, game.mouse_hitbox) or hitellipse(shape.expansion_hitbox_3, game.mouse_hitbox)):
                        if game.can_select and game.left_click:
                            game.mouse_layer = shape.layer
                            game.selected_blockchain_id = shape.blockchain_id
                            game.can_select = False

                    if shape.type == 'ellipse' and (hitellipse(shape.hitbox, game.mouse_hitbox) or hitbox(shape.expansion_hitbox, game.mouse_hitbox)):
                        if game.can_select and game.left_click:
                            game.mouse_layer = shape.layer
                            game.selected_blockchain_id = shape.blockchain_id
                            game.can_select = False

                    if shape.type == 'rectangle' and (hitbox(shape.hitbox, game.mouse_hitbox) or hitbox(shape.expansion_hitbox, game.mouse_hitbox)):
                        if game.can_select and game.left_click:
                            game.mouse_layer = shape.layer
                            game.selected_blockchain_id = shape.blockchain_id
                            game.can_select = False

                """Change Shape Sizes"""
                #Hehe later (needs to be run before center movements or the line object blows up due to necessary selection tolerance)
                if shape.type == 'arc':
                    if (hitbox(shape.expansion_hitbox_1, game.mouse_hitbox) or game.altering_point_1) and not (game.moving or game.altering_point_2 or game.altering_point_3) and game.mouse_layer == shape.layer:
                        if game.left_click:
                            game.altering_point_1 = True
                            game.expanding = True
                            shape.x1 += game.change_x
                            shape.y1 += game.change_y
                            if not game.mouse_lock[0]:
                                game.mouse_lock = (True, shape, shape.x1, shape.y1, game.x_mouse, game.y_mouse)
                        else:
                            game.altering_point_1 = False
                            game.expanding = False
                            game.mouse_lock = (False, None, None, None, 0, 0)

                    if (hitbox(shape.expansion_hitbox_2, game.mouse_hitbox) or game.altering_point_2) and not (game.moving or game.altering_point_1 or game.altering_point_3) and game.mouse_layer == shape.layer:
                        if game.left_click:
                            game.altering_point_2 = True
                            game.expanding = True
                            shape.x2 += game.change_x
                            shape.y2 += game.change_y

                            if not game.mouse_lock[0]:
                                game.mouse_lock = (True, shape, shape.x2, shape.y2, game.x_mouse, game.y_mouse)
                        else:
                            game.mouse_lock = (False, None, None, None, 0, 0)
                            game.altering_point_2 = False
                            game.expanding = False

                    if (hitellipse(shape.expansion_hitbox_3, game.mouse_hitbox) or game.altering_point_3) and not (game.moving or game.altering_point_1 or game.altering_point_2) and game.mouse_layer == shape.layer:
                                if game.left_click:
                                    shape.can_lock = False
                                    game.shape_lock = False
                                    game.altering_point_3 = True
                                    game.expanding = True
                                    shape.x3 += game.change_x
                                    shape.y3 += game.change_y
                                
                                else:
                                    shape.can_lock = True
                                    mouse_lock = (False, None, None, None, 0, 0)
                                    game.altering_point_3 = False
                                    game.expanding = False
                else:
                    if(hitbox(shape.expansion_hitbox, game.mouse_hitbox) or game.expanding) and not (game.moving or game.altering_point_1 or game.altering_point_2) and game.mouse_layer == shape.layer:
                        if game.left_click:
                            game.expanding = True
                            if shape.width > 20:
                                shape.width += game.change_x
                                shape.x += game.change_x / 2
                            elif shape.width == 20 and game.change_x > 0:
                                shape.x += game.change_x / 2
                                shape.width += game.change_x
                            else:
                                shape.width = 20
                            
                            if shape.height > 20:
                                shape.height -= game.change_y
                                shape.y += game.change_y / 2
                            elif shape.height == 20 and game.change_y < 0:
                                shape.y += game.change_y / 2
                                shape.height -= game.change_y
                            else:
                                shape.height = 20

                            if not game.mouse_lock[0]:
                                game.mouse_lock = (True, shape, shape.expansion_hitbox[0], shape.expansion_hitbox[1], game.x_mouse, game.y_mouse)
                        else:
                            game.shape_lock = (False, None, None)
                            game.mouse_lock = (False, None, None, None, 0, 0)
                            game.expanding = False

                """Move Shape Centers"""
                if shape.type == 'arc' and shape.locked:
                    if (hitline(shape.hitbox, game.mouse_hitbox) or game.moving) and not (game.altering_point_1 or game.altering_point_2 or game.expanding) and game.mouse_layer == shape.layer:
                        if game.left_click:
                            game.moving = True
                            shape.x1 += game.change_x
                            shape.x2 += game.change_x
                            shape.y1 += game.change_y
                            shape.y2 += game.change_y
                            if not game.mouse_lock[0]:
                                game.mouse_lock = (True, shape, shape.x, shape.y, game.x_mouse, game.y_mouse)
                        else:
                            game.mouse_lock = (False, None, None, None, 0, 0)
                            game.moving = False
                
                elif shape.type == "rectangle":
                    if (hitbox(shape.hitbox, game.mouse_hitbox) or game.moving) and not (game.altering_point_1 or game.altering_point_2 or game.expanding) and game.mouse_layer == shape.layer:
                        if game.left_click:
                            moving = True
                            shape.x += game.change_x
                            shape.y += game.change_y
                            if not game.mouse_lock[0]:
                                game.mouse_lock = (True, shape, shape.x, shape.y, game.x_mouse, game.y_mouse)
                        else:
                            game.mouse_lock = (False, None, None, None, 0, 0)
                            game.moving = False

                elif shape.type == "ellipse":
                    if(hitellipse(shape.hitbox, game.mouse_hitbox) or game.moving) and not (game.altering_point_1 or game.altering_point_2 or game.expanding) and game.mouse_layer == shape.layer:
                        if game.left_click:
                            game.moving = True
                            shape.x += game.change_x
                            shape.y += game.change_y
                            if not game.mouse_lock[0]:
                                game.mouse_lock = (True, shape, shape.x, shape.y, game.x_mouse, game.y_mouse)
                        else:
                            game.mouse_lock = (False, None, None, None, 0, 0)
                            game.moving = False
        counter += game.dt
        gametime_runner()
    simulator_exit()

def drone_flyer(drone, map):
    game.type = "drone_flyer"
    fly_course_name = f"{map}.csv"
    game.current_file = f"Mechatronics II/Drone Course Simulator/Saved Maps/{fly_course_name}"
    process_file_load(game.current_file)

    while game.running:
        critical_events()
        main_screen_background()
        get_user_inputs()
        draw_obstacles()

        drone.draw()

        gametime_runner()
    simulator_exit()

if __name__ == "__main__":
    # When running the script directly -> launch Map Maker
    map_maker()
else:
    # When importing into another script -> prepare for the Drone Flyer
    pass